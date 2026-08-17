//! Supports recovering from some JSON reader errors

use std::{io::Read, str::FromStr};

use crate::reader::{
    IntegerNumber, JsonReader, JsonReaderPosition, ReaderError, ReaderErrorKind,
    UnexpectedStructureKind, ValueType,
};

/*
 * Implementation note:
 * Recovery is intentionally a two-step manual process:
 * - to make it an explicit choice of the user if they do want to recover from a
 *   specific error
 * - if they do not want to recover from a specific error, to allow them to fail fast,
 *   instead of automatically attempting recovery which redundantly skips values and
 *   when reading from a network connection might even block for more data
 */

#[derive(PartialEq, Debug)]
enum StackValue {
    Array,
    Object,
}

/// JSON reader which supports recovery
///
/// Delegates the reader methods to a wrapped JSON reader, and tracks whether an
/// unrecoverable error occurred. Additionally avoids causing most `UnexpectedValueType` and
/// `UnexpectedStructure` errors for the delegate by checking for these situations itself
/// and supporting recovery from them.
///
/// A recovery struct can be obtained with [`Self::create_recovery`].
#[derive(Debug)]
pub(crate) struct RecoverableJsonReader<'j, J: JsonReader + ?Sized> {
    /// The delegate JSON reader; most access to this should go through [`use_delegate`]
    delegate: &'j mut J,
    /// Whether a value was started (possibly even fully consumed); `false` when only peeking
    /// methods were called
    started_value: bool,
    /// Stack of current open JSON arrays and objects
    ///
    /// `Some` if the underlying reader is still recoverable; `None` if it is not recoverable.
    recovery_stack: Option<Vec<StackValue>>,
    /// Whether the delegate reader is currently right before the next object member value
    ///
    /// Has no meaning if the last [`Self::recovery_stack`] value is not `Object`.
    expects_member_value: bool,
}

impl<'j, J: JsonReader + ?Sized> RecoverableJsonReader<'j, J> {
    pub(crate) fn new(delegate: &'j mut J) -> Self {
        RecoverableJsonReader {
            delegate,
            started_value: false,
            recovery_stack: Some(Vec::new()),
            expects_member_value: false,
        }
    }

    pub(crate) fn create_recovery(self) -> Option<ReaderRecovery<'j, J>> {
        self.recovery_stack.map(|stack| {
            let recovery_action = if self.started_value {
                // Note: stack might be empty if value was fully consumed (and Deserialize returned
                // error afterwards), in that case recovery action does not actually do anything;
                // this is fine, it still indicates to the user that recovery was successful and they
                // can continue reading
                RecoveryAction::CloseOpen {
                    stack,
                    expects_member_value: self.expects_member_value,
                }
            } else {
                debug_assert!(stack.is_empty());
                RecoveryAction::SkipValue
            };
            ReaderRecovery {
                json_reader: self.delegate,
                recovery_action,
            }
        })
    }
}

/// Important: The `reading_action` must not use `?`; that would exit the calling function,
/// without properly handling the error and disabling recovery.
/* This is a macro instead of a function for methods returning `&str` */
macro_rules! use_delegate {
    ($self:ident, |$delegate:ident| $reading_action:expr) => {{
        let $delegate = &mut $self.delegate;
        let result = $reading_action;
        // Treat all errors as unrecoverable, even UnexpectedValueType and UnexpectedStructure;
        // for them it depends on the JSON reader implementation and the specific method being called.
        // Instead this recoverable reader already tries to avoid them by checking `peek()` and `has_next()`.
        if result.is_err() {
            $self.recovery_stack = None;
        }
        result
    }}
}

impl<J: JsonReader + ?Sized> RecoverableJsonReader<'_, J> {
    fn stack(&self) -> &Vec<StackValue> {
        self.recovery_stack
            .as_ref()
            .expect("should not have been called after unrecoverable error")
    }

    fn stack_mut(&mut self) -> &mut Vec<StackValue> {
        self.recovery_stack
            .as_mut()
            .expect("should not have been called after unrecoverable error")
    }

    fn is_in_array(&self) -> bool {
        self.stack().last() == Some(&StackValue::Array)
    }

    fn error_location(&self) -> JsonReaderPosition {
        self.delegate.current_position(true)
    }

    /// Called before a JSON value of any type
    fn before_any_value(&mut self) -> Result<(), ReaderError> {
        /*
         * Only check `has_next()` for array; for object it has to be done for the member name
         *
         * If the stack is empty, preventing an error from `has_next()` is not possible / necessary
         * because if the delegate
         * - is at top-level: if there is no next value then there is also nothing to continue
         *   with afterwards (respectively nothing to recover)
         * - is in an array: the user should have called `has_next()` themselves before the
         *   recoverable reader was constructed (that is, the error would have been avoidable)
         * - is in an object: then the delegate would panic because `has_next()` cannot be
         *   called for member value, only for member name
         */
        if self.is_in_array() && !self.has_next()? {
            return Err(ReaderError::new(
                ReaderErrorKind::UnexpectedStructure(
                    UnexpectedStructureKind::FewerElementsThanExpected,
                ),
                self.error_location(),
            ));
        }
        Ok(())
    }

    fn before_value(&mut self, value_type: ValueType) -> Result<(), ReaderError> {
        self.before_any_value()?;

        let peeked = self.peek()?;
        if peeked != value_type {
            return Err(ReaderError::new(
                ReaderErrorKind::UnexpectedValueType {
                    expected: value_type,
                    actual: peeked,
                },
                self.error_location(),
            ));
        }

        self.on_value_started();
        Ok(())
    }

    /// Called right before a value is started to be consumed
    ///
    /// Should only be called once all recoverable checks were done; any subsequent errors should be
    /// either unrecoverable or should occur after some data has actually been consumed.
    fn on_value_started(&mut self) {
        self.started_value = true;

        // If currently inside an object, indicate that member value has been consumed
        // (has no effect if currently not inside object)
        self.expects_member_value = false;
    }

    fn before_name(&mut self) -> Result<(), ReaderError> {
        if !self.has_next()? {
            return Err(ReaderError::new(
                ReaderErrorKind::UnexpectedStructure(
                    UnexpectedStructureKind::FewerElementsThanExpected,
                ),
                self.error_location(),
            ));
        }
        // Note: At this point the name has not actually been consumed yet, but this happens
        // immediately afterwards, and if it fails the recovery stack is cleared anyway
        self.expects_member_value = true;
        Ok(())
    }

    fn before_container_end(&mut self) -> Result<(), ReaderError> {
        if self.has_next()? {
            return Err(ReaderError::new(
                ReaderErrorKind::UnexpectedStructure(
                    UnexpectedStructureKind::MoreElementsThanExpected,
                ),
                self.error_location(),
            ));
        }
        self.stack_mut()
            .pop()
            .expect("Incorrect usage: Currently not inside an array or object");
        // In case the enclosing container is an object, indicate that it does not expect a
        // member value currently (but a member name instead); has no effect if the enclosing
        // container is not an object
        self.expects_member_value = false;
        Ok(())
    }
}

#[cold]
fn panic_unsupported_usage(message: &str) -> ! {
    panic!("Unsupported: {message}")
}

impl<J: JsonReader + ?Sized> JsonReader for RecoverableJsonReader<'_, J> {
    fn peek(&mut self) -> Result<ValueType, ReaderError> {
        use_delegate!(self, |d| d.peek())
    }

    fn begin_object(&mut self) -> Result<(), ReaderError> {
        self.before_value(ValueType::Object)?;
        use_delegate!(self, |d| d.begin_object())?;
        self.stack_mut().push(StackValue::Object);
        // Indicate that next member name is expected
        self.expects_member_value = false;
        Ok(())
    }

    fn end_object(&mut self) -> Result<(), ReaderError> {
        self.before_container_end()?;
        use_delegate!(self, |d| d.end_object())?;
        Ok(())
    }

    fn begin_array(&mut self) -> Result<(), ReaderError> {
        self.before_value(ValueType::Array)?;
        use_delegate!(self, |d| d.begin_array())?;
        self.stack_mut().push(StackValue::Array);
        Ok(())
    }

    fn end_array(&mut self) -> Result<(), ReaderError> {
        self.before_container_end()?;
        use_delegate!(self, |d| d.end_array())?;
        Ok(())
    }

    fn has_next(&mut self) -> Result<bool, ReaderError> {
        use_delegate!(self, |d| d.has_next())
    }

    fn next_name(&mut self) -> Result<&str, ReaderError> {
        self.before_name()?;
        use_delegate!(self, |d| d.next_name())
    }

    fn next_name_owned(&mut self) -> Result<String, ReaderError> {
        self.before_name()?;
        use_delegate!(self, |d| d.next_name_owned())
    }

    fn next_str(&mut self) -> Result<&str, ReaderError> {
        self.before_value(ValueType::String)?;
        use_delegate!(self, |d| d.next_str())
    }

    fn next_string(&mut self) -> Result<String, ReaderError> {
        self.before_value(ValueType::String)?;
        use_delegate!(self, |d| d.next_string())
    }

    fn next_string_reader(&mut self) -> Result<impl Read + '_, ReaderError> {
        self.before_value(ValueType::String)?;
        Ok(RecoverableStringValueReader {
            delegate: use_delegate!(self, |d| d.next_string_reader())?,
            // All string reading errors are unrecoverable
            on_error: || self.recovery_stack = None,
        })
    }

    fn next_number_as_str(&mut self) -> Result<&str, ReaderError> {
        self.before_value(ValueType::Number)?;
        use_delegate!(self, |d| d.next_number_as_str())
    }

    fn next_number_as_string(&mut self) -> Result<String, ReaderError> {
        self.before_value(ValueType::Number)?;
        use_delegate!(self, |d| d.next_number_as_string())
    }

    fn next_bool(&mut self) -> Result<bool, ReaderError> {
        self.before_value(ValueType::Boolean)?;
        use_delegate!(self, |d| d.next_bool())
    }

    fn next_null(&mut self) -> Result<(), ReaderError> {
        self.before_value(ValueType::Null)?;
        use_delegate!(self, |d| d.next_null())
    }

    // Don't override `deserialize_next` because for recovery any errors from the Deserialize
    // should not be tracked because they don't prevent recovery
    // Instead rely on the default implementation which delegates to all the other implemented
    // methods here and which track whether recovery is possible

    fn skip_name(&mut self) -> Result<(), ReaderError> {
        self.before_name()?;
        use_delegate!(self, |d| d.skip_name())
    }

    fn skip_value(&mut self) -> Result<(), ReaderError> {
        self.before_any_value()?;
        self.on_value_started();
        use_delegate!(self, |d| d.skip_value())
    }

    fn skip_to_top_level(&mut self) -> Result<(), ReaderError> {
        // Skipping to top-level using the delegate might skip further than the recovery
        // stack, causing unspecified behavior for recovery
        // Note: Alternative would be to skip to the top-level of `self.recovery_stack`;
        //   not sure though if that would be the correct / desired behavior
        panic_unsupported_usage("Recoverable reader cannot skip to top-level")
    }

    /*
     * Override default impl; that impl delegates to the other methods here so it would consider
     * some reader errors to be recoverable. However, because `transfer_to` writes to a JSON
     * writer it has side-effects (the JSON data being written) and therefore recovery should
     * not be possible since it is unknown how much data has been written already.
     * (Though most likely these recoverable reader errors cannot actually occur because `transfer_to`
     * transfers untyped JSON data, without expecting any specific structure or value types.)
     *
     * Similarly don't allow recovery if writer error occurred (even though technically reader
     * is still usable); that would be confusing and error-prone.
     */
    fn transfer_to<W: crate::writer::JsonWriter>(
        &mut self,
        json_writer: &mut W,
    ) -> Result<(), super::TransferError> {
        self.before_any_value()?;
        self.on_value_started();
        use_delegate!(self, |d| d.transfer_to(json_writer))
    }

    fn consume_trailing_whitespace(self) -> Result<(), ReaderError> {
        // If it could consume trailing whitespace, then this would happen after the last top-level
        // value, and there would be no point in using recoverable reader in the first place
        // Additionally, this cannot be implemented because `consume_trailing_whitespace` consumes
        // `self` but `self.delegate` is only a reference and cannot be consumed
        panic_unsupported_usage("Recoverable reader cannot consume trailing whitespace")
    }

    fn current_position(&self, include_path: bool) -> JsonReaderPosition {
        self.delegate.current_position(include_path)
    }

    /*
     * Override and delegate some default method impls
     * To benefit from potentially optimized impls in the delegate JSON reader.
     */

    fn next_number<T: FromStr>(&mut self) -> Result<Result<T, T::Err>, ReaderError> {
        self.before_value(ValueType::Number)?;
        use_delegate!(self, |d| d.next_number())
    }

    fn next_number_int<N: IntegerNumber>(&mut self) -> Result<N, ReaderError> {
        self.before_value(ValueType::Number)?;
        use_delegate!(self, |d| d.next_number_int())
    }

    // Don't override `seek_to` (and use delegate impl), because then recovery is not possible
    // since all errors reported by the delegate `seek_to` would be treated as unrecoverable.
    // It would also lead to the recovery stack getting out of sync because this recoverable
    // reader would be unaware of opened arrays and object.
    // Instead use default impl which delegates to all the other recoverable methods implemented here.

    // Don't override `seek_back` (and use delegate impl), because it closes arrays and objects
    // but this recoverable reader would be unaware of it then, and its recovery stack would
    // get out of sync.
}

struct RecoverableStringValueReader<R: Read, E: FnMut()> {
    delegate: R,
    on_error: E,
}
impl<R: Read, E: FnMut()> Read for RecoverableStringValueReader<R, E> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let result = self.delegate.read(buf);
        if result.is_err() {
            (self.on_error)()
        }
        result
    }
}

#[derive(Debug)]
enum RecoveryAction {
    /// Skip the complete next value
    SkipValue,
    /// For all open arrays and objects, skip their remaining elements and close them
    ///
    /// The stack must be processed in reverse order.
    CloseOpen {
        stack: Vec<StackValue>,
        /// If the last stack value is `Object` (i.e. the first one to close), indicates whether
        /// it currently expects a member name (`false`) or member value (`true`)
        ///
        /// For all other stack values this has no meaning.
        expects_member_value: bool,
    },
}

/// Supports recovering a `JsonReader`
///
/// This struct is used by [`JsonReader::deserialize_next_recoverable`], see its documentation
/// for more information.
///
/// This struct holds a reference to the JSON reader to recover, intentionally preventing
/// any other actions on the reader until [`recover_reader`](Self::recover_reader) is used.
#[derive(Debug)]
pub struct ReaderRecovery<'j, J: JsonReader + ?Sized> {
    // Keeps a reference to the reader instead of taking it as argument for the recover method
    // to ensure the recovery is performed on the same reader and not an unrelated one, and
    // to prevent user (through borrow checker) from using reader while recovery is still in scope
    json_reader: &'j mut J,
    recovery_action: RecoveryAction,
}

impl<J: JsonReader + ?Sized> ReaderRecovery<'_, J> {
    /// Recovers the JSON reader
    ///
    /// If this method returns `Ok`, the reader was successfully recovered and it can continue
    /// to be used. If `Err` is returned, recovery failed and the JSON reader must not be
    /// used any further. That error is the one which occurred during recovery, which is
    /// different from the one which initially made recovery necessary.
    /* Consumes `self` to allow using recovery only once */
    pub fn recover_reader(self) -> Result<(), ReaderError> {
        match &self.recovery_action {
            RecoveryAction::SkipValue => self.json_reader.skip_value()?,
            RecoveryAction::CloseOpen {
                stack,
                expects_member_value,
            } => {
                // If the reader just started an object member and only consumed its name but not the value yet,
                // skip it; the loop below assumes that it can always skip complete member name + value pairs
                if stack.last() == Some(&StackValue::Object) && *expects_member_value {
                    self.json_reader.skip_value()?;
                }

                // Close open arrays and objects in reverse order
                for stack_value in stack.iter().rev() {
                    match stack_value {
                        StackValue::Array => {
                            // Skip remaining items
                            while self.json_reader.has_next()? {
                                self.json_reader.skip_value()?;
                            }
                            self.json_reader.end_array()?;
                        }
                        StackValue::Object => {
                            // Skip remaining members
                            while self.json_reader.has_next()? {
                                self.json_reader.skip_name()?;
                                self.json_reader.skip_value()?;
                            }
                            self.json_reader.end_object()?;
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::{
        error::Error,
        io::{Write, sink},
    };

    use super::*;
    use crate::{
        reader::{JsonStreamReader, TransferError, json_path::json_path},
        writer::JsonStreamWriter,
    };

    // Test some of the JSON reader methods here which are either difficult to test extensively
    // in the code using recovery (currently only Deserialize integration), or are currently not
    // used at all and therefore not covered by any other test

    #[test]
    fn next_string_reader() -> Result<(), Box<dyn Error>> {
        let mut json_reader = JsonStreamReader::new(r#"["test", 1]"#.as_bytes());
        let mut json_reader = RecoverableJsonReader::new(&mut json_reader);
        json_reader.begin_array()?;

        let mut string_reader = json_reader.next_string_reader()?;
        let mut str_value = String::new();
        string_reader.read_to_string(&mut str_value)?;
        assert_eq!(str_value, "test");
        drop(string_reader);
        // Should still be recoverable
        assert_eq!(json_reader.recovery_stack, Some(vec![StackValue::Array]));

        assert_eq!(json_reader.next_number_as_str()?, "1");

        json_reader.end_array()?;
        Ok(())
    }

    #[test]
    fn next_string_reader_error() -> Result<(), Box<dyn Error>> {
        // String with invalid escape sequence
        let mut json_reader = JsonStreamReader::new(r#"["test \x"]"#.as_bytes());
        let mut json_reader = RecoverableJsonReader::new(&mut json_reader);
        json_reader.begin_array()?;

        let mut string_reader = json_reader.next_string_reader()?;
        let mut str_value = String::new();
        let result = string_reader.read_to_string(&mut str_value);
        assert_eq!(
            result.unwrap_err().to_string(),
            "JSON syntax error UnknownEscapeSequence at path '$[0]', line 0, column 7 (data pos 7)"
        );
        drop(string_reader);
        // Reader should not be recoverable anymore
        assert_eq!(json_reader.recovery_stack, None);

        Ok(())
    }

    #[test]
    fn transfer_to_recovery() -> Result<(), Box<dyn Error>> {
        let mut json_reader = JsonStreamReader::new("[]".as_bytes());
        let mut json_reader = RecoverableJsonReader::new(&mut json_reader);
        json_reader.begin_array()?;

        let mut json_writer = JsonStreamWriter::new(sink());
        match json_reader.transfer_to(&mut json_writer) {
            Err(TransferError::ReaderError(reader_error)) => {
                assert_eq!(
                    reader_error.to_string(),
                    "unexpected JSON structure FewerElementsThanExpected at path '$[0]', line 0, column 1 (data pos 1)"
                );
            }
            r => panic!("unexpected result: {r:?}"),
        }

        // Recovery should be possible because error occurred before `transfer_to` actually transferred any data
        // TODO: Does this really make sense, or should `transfer_to` generally not support recovery?
        //   Note also that the error here would have been avoidable if the calling code had checked `has_next` first
        assert_eq!(json_reader.recovery_stack, Some(vec![StackValue::Array]));

        Ok(())
    }

    #[test]
    fn transfer_to_writer_error() -> Result<(), Box<dyn Error>> {
        /// Writer which always returns an error
        struct FailingWriter;
        impl Write for FailingWriter {
            fn write(&mut self, _buf: &[u8]) -> std::io::Result<usize> {
                Err(std::io::Error::other("custom error"))
            }

            fn flush(&mut self) -> std::io::Result<()> {
                Err(std::io::Error::other("custom error"))
            }
        }

        let mut json_reader = JsonStreamReader::new("[1]".as_bytes());
        let mut json_reader = RecoverableJsonReader::new(&mut json_reader);
        json_reader.begin_array()?;

        let mut json_writer = JsonStreamWriter::new(FailingWriter);
        match json_reader.transfer_to(&mut json_writer) {
            Err(TransferError::WriterError(writer_error)) => {
                assert_eq!(writer_error.to_string(), "custom error");
            }
            r => panic!("unexpected result: {r:?}"),
        }

        // No recovery should be possible
        assert_eq!(json_reader.recovery_stack, None);

        Ok(())
    }

    #[test]
    fn seek_to() -> Result<(), Box<dyn Error>> {
        let mut json_reader = JsonStreamReader::new(r#"[1, {"a": 2}]"#.as_bytes());
        let mut json_reader = RecoverableJsonReader::new(&mut json_reader);

        let json_path = json_path![1, "a".to_owned()];
        json_reader.seek_to(&json_path)?;
        // Verify that recovery stack was properly updated
        assert_eq!(
            json_reader.recovery_stack,
            Some(vec![StackValue::Array, StackValue::Object])
        );

        assert_eq!(json_reader.next_number_as_str()?, "2");

        json_reader.seek_back(&json_path)?;
        // Verify that recovery stack was properly updated
        assert_eq!(json_reader.recovery_stack, Some(vec![]));

        Ok(())
    }

    #[test]
    fn seek_to_recoverable_error() {
        let mut json_reader = JsonStreamReader::new(r#"[1, {"a": 2}]"#.as_bytes());
        let mut json_reader = RecoverableJsonReader::new(&mut json_reader);

        let json_path = json_path![1, "b".to_owned()];
        let result = json_reader.seek_to(&json_path);
        assert_eq!(
            result.unwrap_err().to_string(),
            "unexpected JSON structure MissingObjectMember(\"b\") at path '$[1].a', line 0, column 11 (data pos 11)"
        );

        // Verify that error is recoverable
        assert_eq!(
            json_reader.recovery_stack,
            Some(vec![StackValue::Array, StackValue::Object])
        );
    }

    #[test]
    #[should_panic(expected = "Unsupported: Recoverable reader cannot skip to top-level")]
    fn skip_to_top_level() {
        let mut json_reader = JsonStreamReader::new("[".as_bytes());
        let mut json_reader = RecoverableJsonReader::new(&mut json_reader);
        json_reader.begin_array().unwrap();
        let _ = json_reader.skip_to_top_level();
    }

    #[test]
    #[should_panic(expected = "Unsupported: Recoverable reader cannot consume trailing whitespace")]
    fn consume_trailing_whitespace() {
        let mut json_reader = JsonStreamReader::new("1".as_bytes());
        let mut json_reader = RecoverableJsonReader::new(&mut json_reader);
        json_reader.skip_value().unwrap();
        let _ = json_reader.consume_trailing_whitespace();
    }
}
