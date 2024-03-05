//! JSON writer variant which is easier to use than [`JsonWriter`]
//!
//! The main entrypoint is [`SimpleJsonWriter`], all other structs and traits
//! are used by it for writing certain JSON value types.
//!
//! ----
//!
//! **🔬 Experimental**\
//! This API and the naming is currently experimental, please provide feedback [here](https://github.com/Marcono1234/struson/issues/34).
//! Any feedback is appreciated!

use std::{error::Error, io::Write};

use self::error_safe_writer::ErrorSafeJsonWriter;
use crate::writer::{
    FiniteNumber, FloatingPointNumber, JsonNumberError, JsonStreamWriter, JsonWriter,
};

type IoError = std::io::Error;

/// Writer for a JSON value
pub trait ValueWriter<J: JsonWriter> {
    /// Writes a JSON null value
    fn write_null(self) -> Result<(), IoError>;

    /// Writes a JSON boolean value
    fn write_bool(self, value: bool) -> Result<(), IoError>;

    /// Writes a JSON string value
    fn write_string(self, value: &str) -> Result<(), IoError>;

    /// Writes a JSON number value
    fn write_number<N: FiniteNumber>(self, value: N) -> Result<(), IoError>;

    /// Writes a floating point JSON number value
    ///
    /// Returns an error if the number is non-finite and therefore cannot be written
    /// as JSON number value.
    fn write_fp_number<N: FloatingPointNumber>(self, value: N) -> Result<(), JsonNumberError>;

    /// Writes the string representation of a JSON number value
    ///
    /// Returns an error if the string is not a valid JSON number value.
    fn write_number_string(self, value: &str) -> Result<(), JsonNumberError>;

    /// Serializes a Serde [`Serialize`](serde::ser::Serialize) as next value
    ///
    /// This method is part of the optional Serde integration feature, see the
    /// [`serde` module](crate::serde) of this crate for more information.
    ///
    /// # Examples
    /// ```
    /// # use struson::writer::simple::*;
    /// # use serde::*;
    /// let mut writer = Vec::<u8>::new();
    /// let json_writer = SimpleJsonWriter::new(&mut writer);
    ///
    /// #[derive(Serialize)]
    /// struct MyStruct {
    ///     text: String,
    ///     number: u64,
    /// }
    ///
    /// let value = MyStruct {
    ///     text: "some text".to_owned(),
    ///     number: 5,
    /// };
    /// json_writer.write_serialize(&value)?;
    ///
    /// let json = String::from_utf8(writer)?;
    /// assert_eq!(
    ///     json,
    ///     r#"{"text":"some text","number":5}"#
    /// );
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[cfg(feature = "serde")]
    fn write_serialize<S: serde::ser::Serialize>(
        self,
        value: &S,
    ) -> Result<(), crate::serde::SerializerError>;

    /// Writes a JSON array
    ///
    /// # Examples
    /// ```
    /// # use struson::writer::simple::*;
    /// let mut writer = Vec::<u8>::new();
    /// let json_writer = SimpleJsonWriter::new(&mut writer);
    /// json_writer.write_array(|array_writer| {
    ///     array_writer.write_number(1)?;
    ///     array_writer.write_bool(true)?;
    ///     Ok(())
    /// })?;
    ///
    /// let json = String::from_utf8(writer)?;
    /// assert_eq!(json, "[1,true]");
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn write_array(
        self,
        f: impl FnOnce(&mut ArrayWriter<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>>;

    /// Writes a JSON object
    ///
    /// # Examples
    /// ```
    /// # use struson::writer::simple::*;
    /// let mut writer = Vec::<u8>::new();
    /// let json_writer = SimpleJsonWriter::new(&mut writer);
    /// json_writer.write_object(|object_writer| {
    ///     object_writer.write_number_member("a", 1)?;
    ///     object_writer.write_bool_member("b", true)?;
    ///     Ok(())
    /// })?;
    ///
    /// let json = String::from_utf8(writer)?;
    /// assert_eq!(json, r#"{"a":1,"b":true}"#);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn write_object(
        self,
        f: impl FnOnce(&mut ObjectWriter<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>>;
}

fn write_array<J: JsonWriter>(
    json_writer: &mut ErrorSafeJsonWriter<J>,
    f: impl FnOnce(&mut ArrayWriter<'_, J>) -> Result<(), Box<dyn Error>>,
) -> Result<(), Box<dyn Error>> {
    json_writer.begin_array()?;
    let mut array_writer = ArrayWriter { json_writer };
    f(&mut array_writer)?;
    json_writer.end_array()?;
    Ok(())
}

fn write_object<J: JsonWriter>(
    json_writer: &mut ErrorSafeJsonWriter<J>,
    f: impl FnOnce(&mut ObjectWriter<'_, J>) -> Result<(), Box<dyn Error>>,
) -> Result<(), Box<dyn Error>> {
    json_writer.begin_object()?;
    let mut object_writer = ObjectWriter { json_writer };
    f(&mut object_writer)?;
    json_writer.end_object()?;
    Ok(())
}

mod error_safe_writer {
    use std::io::ErrorKind;

    use super::*;
    use crate::writer::{IoError, UnreachableStringValueWriter};

    type StoredIoError = (ErrorKind, String);

    fn convert_io_error(error: &IoError) -> StoredIoError {
        (error.kind(), error.to_string())
    }

    fn convert_number_error(error: &JsonNumberError) -> StoredIoError {
        match error {
            JsonNumberError::InvalidNumber(message) => (ErrorKind::Other, message.clone()),
            JsonNumberError::IoError(e) => convert_io_error(e),
        }
    }

    fn error_from_stored(error: &StoredIoError) -> IoError {
        // Report as `Other` kind (and with custom message) to avoid caller indefinitely retrying
        // because it considers the original error kind as safe to retry
        // And also because the original error might have been related to originally provided data
        // (e.g. invalid UTF-8 data) and is unrelated to the now called JSON writer method
        IoError::other(format!("previous error '{}': {}", error.0, error.1.clone()))
    }

    /// If previously an error had occurred, returns that error. Otherwise uses the delegate
    /// writer and in case of an error stores it to prevent subsequent usage.
    /* This is a macro instead of a function to support error conversion */
    macro_rules! use_delegate {
        ($self:ident, |$json_writer:ident| $writing_action:expr, |$original_error:ident| $original_error_converter:expr, |$stored_error:ident| $stored_error_converter:expr) => {
            if let Some(error) = &$self.error {
                // Report as `Other` kind (and with custom message) to avoid caller indefinitely retrying
                // because it considers the original error kind as safe to retry
                // And also because the original error might have been related to originally provided data
                // (e.g. invalid UTF-8 data) and is unrelated to the now called JSON writer method
                let $stored_error = error_from_stored(error);
                Err($stored_error_converter)
            } else {
                let $json_writer = &mut $self.delegate;
                let result = $writing_action;
                if let Err($original_error) = &result {
                    $self.error = Some($original_error_converter);
                }
                result
            }
        };
        ($self:ident, |$json_writer:ident| $writing_action:expr) => {
            use_delegate!(
                $self,
                |$json_writer| $writing_action,
                |original_error| convert_io_error(original_error),
                |stored_error| stored_error
            )
        }
    }

    /// [`JsonWriter`] implementation which in case of errors keeps returning the error and does
    /// not use the underlying JSON writer anymore
    ///
    /// This is mainly to protect against user-provided closures or functions which accidentally
    /// discard and not propagate writer errors, which could lead to subsequent panics. How exactly
    /// this writer repeats errors or what information it preserves is unspecified; users should
    /// always propagate writer errors and not (intentionally) rely on this safeguard here.
    #[derive(Debug)]
    pub(super) struct ErrorSafeJsonWriter<J: JsonWriter> {
        pub(super) delegate: J,
        // Store as `IoError` (destructured as `(kind, message)`) because that is the common error type
        // supported by all methods
        pub(super) error: Option<StoredIoError>,
    }

    impl<J: JsonWriter> JsonWriter for ErrorSafeJsonWriter<J> {
        fn begin_object(&mut self) -> Result<(), IoError> {
            use_delegate!(self, |w| w.begin_object())
        }

        fn end_object(&mut self) -> Result<(), IoError> {
            use_delegate!(self, |w| w.end_object())
        }

        fn begin_array(&mut self) -> Result<(), IoError> {
            use_delegate!(self, |w| w.begin_array())
        }

        fn end_array(&mut self) -> Result<(), IoError> {
            use_delegate!(self, |w| w.end_array())
        }

        fn name(&mut self, name: &str) -> Result<(), IoError> {
            use_delegate!(self, |w| w.name(name))
        }

        fn null_value(&mut self) -> Result<(), IoError> {
            use_delegate!(self, |w| w.null_value())
        }

        fn bool_value(&mut self, value: bool) -> Result<(), IoError> {
            use_delegate!(self, |w| w.bool_value(value))
        }

        fn string_value(&mut self, value: &str) -> Result<(), IoError> {
            use_delegate!(self, |w| w.string_value(value))
        }

        fn string_value_writer(&mut self) -> Result<UnreachableStringValueWriter, IoError> {
            unreachable!("not used by Simple API")
            // If this is used in the future, the string value writer must track all of its errors
            // and then store them here as error as well, to prevent further JSON writer usage
        }

        fn number_value_from_string(&mut self, value: &str) -> Result<(), JsonNumberError> {
            use_delegate!(
                self,
                |w| w.number_value_from_string(value),
                |original_error| convert_number_error(original_error),
                |stored_error| JsonNumberError::IoError(stored_error)
            )
        }

        fn number_value<N: FiniteNumber>(&mut self, value: N) -> Result<(), IoError> {
            use_delegate!(self, |w| w.number_value(value))
        }

        fn fp_number_value<N: FloatingPointNumber>(
            &mut self,
            value: N,
        ) -> Result<(), JsonNumberError> {
            use_delegate!(
                self,
                |w| w.fp_number_value(value),
                |original_error| convert_number_error(original_error),
                |stored_error| JsonNumberError::IoError(stored_error)
            )
        }

        #[cfg(feature = "serde")]
        fn serialize_value<S: serde::ser::Serialize>(
            &mut self,
            value: &S,
        ) -> Result<(), crate::serde::SerializerError> {
            use crate::serde::SerializerError;

            use_delegate!(
                self,
                |w| w.serialize_value(value),
                |original_error| match original_error {
                    SerializerError::IoError(e) => convert_io_error(e),
                    e => (ErrorKind::Other, e.to_string()),
                },
                // Note: Could also create `SerializerError::Custom` instead
                |stored_error| SerializerError::IoError(stored_error)
            )
        }

        fn finish_document(self) -> Result<(), IoError> {
            // Special code because this method consumes `self`
            if let Some(error) = self.error {
                return Err(error_from_stored(&error));
            }
            self.delegate.finish_document()
        }
    }
}

/// JSON writer variant which is easier to use than [`JsonWriter`]
///
/// This JSON writer variant ensures correct usage at compile-time making it easier and less
/// error-prone to use than [`JsonWriter`], which validates correct usage at runtime and panics
/// on incorrect usage. However, this comes at the cost of `SimpleJsonWriter` being less flexible
/// to use, and it not offerring all features of [`JsonWriter`].
///
/// When an error is returned by one of the methods of the writer, the error should be propagated
/// (for example by using Rust's `?` operator), processing should be aborted and the writer should
/// not be used any further.
///
/// # Examples
/// ```
/// # use struson::writer::simple::*;
/// // In this example JSON bytes are stored in a Vec;
/// // normally they would be written to a file or network connection
/// let mut writer = Vec::<u8>::new();
/// let json_writer = SimpleJsonWriter::new(&mut writer);
/// json_writer.write_object(|object_writer| {
///     object_writer.write_number_member("a", 1)?;
///     object_writer.write_bool_member("b", true)?;
///     Ok(())
/// })?;
///
/// let json = String::from_utf8(writer)?;
/// assert_eq!(json, r#"{"a":1,"b":true}"#);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Debug)]
pub struct SimpleJsonWriter<J: JsonWriter> {
    json_writer: ErrorSafeJsonWriter<J>,
}
impl<J: JsonWriter> SimpleJsonWriter<J> {
    /// Creates a new `SimpleJsonWriter` from the given [`JsonWriter`]
    ///
    /// The `JsonWriter` acts as delegate which performs the actual JSON writing. It should
    /// not have written any JSON data yet, otherwise the behavior of the created `SimpleJsonWriter`
    /// is unspecified and it may panic.
    ///
    /// # Examples
    /// ```
    /// # use struson::writer::*;
    /// # use struson::writer::simple::*;
    /// let mut writer = Vec::<u8>::new();
    /// # #[allow(unused_variables)]
    /// let json_writer = SimpleJsonWriter::from_json_writer(
    ///     JsonStreamWriter::new_custom(
    ///         &mut writer,
    ///         WriterSettings {
    ///             pretty_print: true,
    ///             // For all other settings use the default
    ///             ..Default::default()
    ///         },
    ///     )
    /// );
    /// ```
    pub fn from_json_writer(json_writer: J) -> Self {
        SimpleJsonWriter {
            json_writer: ErrorSafeJsonWriter {
                delegate: json_writer,
                error: None,
            },
        }
    }
}
impl<W: Write> SimpleJsonWriter<JsonStreamWriter<W>> {
    /// Creates a new JSON writer
    ///
    /// The JSON data will be written UTF-8 encoded to the writer. Internally this creates a [`JsonStreamWriter`]
    /// which acts as delegate; see its documentation for more information about the writing behavior.
    pub fn new(writer: W) -> Self {
        SimpleJsonWriter::from_json_writer(JsonStreamWriter::new(writer))
    }
}

// These methods all call `json_writer.finish_document()` because `SimpleJsonWriter`
// is intended to be used for top-level value
impl<J: JsonWriter> ValueWriter<J> for SimpleJsonWriter<J> {
    fn write_null(mut self) -> Result<(), IoError> {
        self.json_writer.null_value()?;
        self.json_writer.finish_document()
    }

    fn write_bool(mut self, value: bool) -> Result<(), IoError> {
        self.json_writer.bool_value(value)?;
        self.json_writer.finish_document()
    }

    fn write_string(mut self, value: &str) -> Result<(), IoError> {
        self.json_writer.string_value(value)?;
        self.json_writer.finish_document()
    }

    fn write_number<N: FiniteNumber>(mut self, value: N) -> Result<(), IoError> {
        self.json_writer.number_value(value)?;
        self.json_writer.finish_document()
    }

    fn write_fp_number<N: FloatingPointNumber>(mut self, value: N) -> Result<(), JsonNumberError> {
        self.json_writer.fp_number_value(value)?;
        // Using `?` here is a bit misleading since that will wrap an IO error from `finish_document()`
        // in a `JsonNumberError`, but that is probably acceptable
        self.json_writer.finish_document()?;
        Ok(())
    }

    fn write_number_string(mut self, value: &str) -> Result<(), JsonNumberError> {
        self.json_writer.number_value_from_string(value)?;
        // Using `?` here is a bit misleading since that will wrap an IO error from `finish_document()`
        // in a `JsonNumberError`, but that is probably acceptable
        self.json_writer.finish_document()?;
        Ok(())
    }

    #[cfg(feature = "serde")]
    fn write_serialize<S: serde::ser::Serialize>(
        mut self,
        value: &S,
    ) -> Result<(), crate::serde::SerializerError> {
        self.json_writer.serialize_value(value)?;
        // Using `?` here is a bit misleading since that will wrap an IO error from `finish_document()`
        // in a `SerializerError`, but that is probably acceptable
        self.json_writer.finish_document()?;
        Ok(())
    }

    fn write_array(
        mut self,
        f: impl FnOnce(&mut ArrayWriter<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        write_array(&mut self.json_writer, f)?;
        self.json_writer.finish_document()?;
        Ok(())
    }

    fn write_object(
        mut self,
        f: impl FnOnce(&mut ObjectWriter<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        write_object(&mut self.json_writer, f)?;
        self.json_writer.finish_document()?;
        Ok(())
    }
}

/// Writer for JSON array items
///
/// This struct is used by [`ValueWriter::write_array`].
#[derive(Debug)]
pub struct ArrayWriter<'a, J: JsonWriter> {
    json_writer: &'a mut ErrorSafeJsonWriter<J>,
}
// Implement for `&mut ArrayWriter` to allow writing multiple values instead of just one
impl<J: JsonWriter> ValueWriter<J> for &mut ArrayWriter<'_, J> {
    fn write_null(self) -> Result<(), IoError> {
        self.json_writer.null_value()
    }

    fn write_bool(self, value: bool) -> Result<(), IoError> {
        self.json_writer.bool_value(value)
    }

    fn write_string(self, value: &str) -> Result<(), IoError> {
        self.json_writer.string_value(value)
    }

    fn write_number<N: FiniteNumber>(self, value: N) -> Result<(), IoError> {
        self.json_writer.number_value(value)
    }

    fn write_fp_number<N: FloatingPointNumber>(self, value: N) -> Result<(), JsonNumberError> {
        self.json_writer.fp_number_value(value)?;
        Ok(())
    }

    fn write_number_string(self, value: &str) -> Result<(), JsonNumberError> {
        self.json_writer.number_value_from_string(value)?;
        Ok(())
    }

    #[cfg(feature = "serde")]
    fn write_serialize<S: serde::ser::Serialize>(
        self,
        value: &S,
    ) -> Result<(), crate::serde::SerializerError> {
        self.json_writer.serialize_value(value)?;
        Ok(())
    }

    fn write_array(
        self,
        f: impl FnOnce(&mut ArrayWriter<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        write_array(self.json_writer, f)
    }

    fn write_object(
        self,
        f: impl FnOnce(&mut ObjectWriter<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        write_object(self.json_writer, f)
    }
}

/// Writer for JSON object members
///
/// Each method writes a JSON object member in the form of a name-value pair.
/// For example the member `"a": 1` consists of the name "a" and the value 1,
/// which can be written using [`write_number_member`](Self::write_number_member).
///
/// This struct is used by [`ValueWriter::write_object`].
#[derive(Debug)]
pub struct ObjectWriter<'a, J: JsonWriter> {
    json_writer: &'a mut ErrorSafeJsonWriter<J>,
}
impl<J: JsonWriter> ObjectWriter<'_, J> {
    /// Writes a member with JSON null as value
    pub fn write_null_member(&mut self, name: &str) -> Result<(), IoError> {
        self.json_writer.name(name)?;
        self.json_writer.null_value()
    }

    /// Writes a member with a JSON boolean as value
    pub fn write_bool_member(&mut self, name: &str, value: bool) -> Result<(), IoError> {
        self.json_writer.name(name)?;
        self.json_writer.bool_value(value)
    }

    /// Writes a member with a JSON string as value
    pub fn write_string_member(&mut self, name: &str, value: &str) -> Result<(), IoError> {
        self.json_writer.name(name)?;
        self.json_writer.string_value(value)
    }

    /// Writes a member with a JSON number as value
    pub fn write_number_member<N: FiniteNumber>(
        &mut self,
        name: &str,
        value: N,
    ) -> Result<(), IoError> {
        self.json_writer.name(name)?;
        self.json_writer.number_value(value)
    }

    /// Writes a member with a floating point JSON number as value
    ///
    /// Returns an error if the number is non-finite and therefore cannot be written
    /// as JSON number value.
    pub fn write_fp_number_member<N: FloatingPointNumber>(
        &mut self,
        name: &str,
        value: N,
    ) -> Result<(), JsonNumberError> {
        self.json_writer.name(name)?;
        self.json_writer.fp_number_value(value)
    }

    /// Writes a member with the string representation of a JSON number as value
    ///
    /// Returns an error if the string is not a valid JSON number value.
    pub fn write_number_string_member(
        &mut self,
        name: &str,
        value: &str,
    ) -> Result<(), JsonNumberError> {
        self.json_writer.name(name)?;
        self.json_writer.number_value_from_string(value)
    }

    /// Writes a member with a Serde [`Serialize`](serde::ser::Serialize) as value
    ///
    /// This method is part of the optional Serde integration feature, see the
    /// [`serde` module](crate::serde) of this crate for more information.
    /*
     * This is called 'serialize*d*' because 'serialize_member' might be a bit misleading since
     * it is not serializing the whole member but only the member value
     */
    #[cfg(feature = "serde")]
    pub fn write_serialized_member<S: serde::ser::Serialize>(
        &mut self,
        name: &str,
        value: &S,
    ) -> Result<(), crate::serde::SerializerError> {
        self.json_writer.name(name)?;
        self.json_writer.serialize_value(value)
    }

    /// Writes a member with a JSON array as value
    pub fn write_array_member(
        &mut self,
        name: &str,
        f: impl FnOnce(&mut ArrayWriter<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        self.json_writer.name(name)?;
        write_array(self.json_writer, f)
    }

    /// Writes a member with a JSON object as value
    pub fn write_object_member(
        &mut self,
        name: &str,
        f: impl FnOnce(&mut ObjectWriter<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        self.json_writer.name(name)?;
        write_object(self.json_writer, f)
    }
}
