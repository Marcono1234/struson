//! Streaming implementation of [`JsonReader`]

use std::io::ErrorKind;

use thiserror::Error;

use self::bytes_value_reader::{
    AsUnicodeEscapeReader, AsUtf8MultibyteReader, BytesValue, BytesValueReader,
};
use super::{json_path::JsonPathPiece, *};
// Ignore false positive for unused import of `json_path!` macro
#[allow(unused_imports)]
use super::json_path::json_path;
use crate::{
    json_number::{consume_json_number, NumberBytesProvider},
    utf8,
    writer::TransferredNumber,
};

#[derive(PartialEq, Clone, Copy, strum::Display, Debug)]
enum PeekedValue {
    ObjectStart,
    ObjectEnd,
    ArrayStart,
    ArrayEnd,
    // Reader state: Opening " has already been consumed
    StringStart,
    NameStart,
    // Reader state: Number has not been consumed yet
    NumberStart,
    Null,
    BooleanTrue,
    BooleanFalse,
}

#[derive(Error, Debug)]
#[error("IO error '{0}' at (roughly) {1}")]
struct ReaderIoError(IoError, JsonReaderPosition);

impl From<ReaderIoError> for ReaderError {
    fn from(value: ReaderIoError) -> Self {
        ReaderError::IoError {
            error: value.0,
            location: value.1,
        }
    }
}

#[derive(Error, Debug)]
enum StringReadingError {
    #[error("syntax error: {0}")]
    SyntaxError(#[from] JsonSyntaxError),
    #[error("{0}")]
    IoError(#[from] ReaderIoError),
}

impl From<StringReadingError> for ReaderError {
    fn from(e: StringReadingError) -> Self {
        match e {
            StringReadingError::SyntaxError(e) => ReaderError::SyntaxError(e),
            StringReadingError::IoError(e) => e.into(),
        }
    }
}

#[derive(PartialEq, Debug)]
enum StackValue {
    Array,
    Object,
}

const READER_BUF_SIZE: usize = 1024;
const INITIAL_VALUE_BYTES_BUF_CAPACITY: usize = 128;

/// A JSON reader implementation which consumes data from a [`Read`]
///
/// This reader internally buffers data so it is normally not necessary to wrap the provided
/// reader in a [`std::io::BufReader`]. However, due to this buffering it should not be
/// attempted to use the provided `Read` after this JSON reader was dropped (in case the
/// `Read` was provided by reference only), unless [`JsonReader::consume_trailing_whitespace`]
/// was called and therefore the end of the `Read` stream was reached. Otherwise due to
/// the buffering it is unpredictable how much additional data this JSON reader has consumed
/// from the `Read`.
///
/// The data provided by the underlying reader is expected to be valid UTF-8 data.
/// The JSON reader methods will return a [`ReaderError::IoError`] if invalid UTF-8 data
/// is detected. A leading byte order mark (BOM) is not allowed.
///
/// If the underlying reader returns an error of kind [`ErrorKind::Interrupted`], this
/// JSON reader will keep retrying to read data.
///
/// # Security
/// Besides UTF-8 validation this JSON reader only implements a basic restriction on JSON numbers,
/// see [`ReaderSettings::restrict_number_values`], but does not implement any other security
/// related measures. In particular it does **not**:
///
/// - Impose a limit on the length of the document
///
///   Especially when the JSON data comes from a compressed data stream (such as gzip) large JSON documents
///   could be used for denial of service attacks.
///
/// - Impose a limit on the nesting depth
///
///   JSON arrays and objects might be arbitrary deeply nested. Trying to process such JSON documents
///   in a recursive way could therefore lead to a stack overflow. While this JSON reader implementation
///   does not use recursive calls, users of this reader must make sure to not use recursive calls
///   either or track and limit the nesting depth.
///
/// - Detect duplicate member names
///
///   The JSON specification allows duplicate member names, but does not dictate how to handle
///   them. Different JSON libraries might therefore handle them in inconsistent ways (for example one
///   using the first occurrence, another one using the last), which could be exploited.
///
/// - Impose a limit on the length on member names and string values, or on arrays and objects
///
///   Especially when the JSON data comes from a compressed data stream (such as gzip) large member names
///   and string values or large arrays and objects could be used for denial of service attacks.
///
/// - Impose restrictions on content of member names and string values
///
///   The only restriction is that member names and string values are valid UTF-8 strings, besides
///   that they can contain any code point. They may contain control characters such as the NULL
///   character (`\0`), code points which are not yet assigned a character or invalid graphemes.
///
/// When processing JSON data from an untrusted source, users of this JSON reader must implement protections
/// against the above mentioned security issues themselves.
pub struct JsonStreamReader<R: Read> {
    // When adding more fields to this struct, adjust the Debug implementation below, if necessary
    reader: R,
    /// Buffer containing some bytes read from [`reader`](Self::reader)
    buf: [u8; READER_BUF_SIZE],
    /// Start index (inclusive) at which data in [`buf`](Self::buf) starts
    buf_pos: usize,
    /// Index (exclusive) up to which [`buf`](Self::buf) is filled
    buf_end_pos: usize,
    /// Whether [`buf`](Self::buf) is currently used by a [`BytesRefProvider::ReaderBuf`]
    buf_used_for_bytes_value: bool,
    reached_eof: bool,
    /// Used as scratch buffer to temporarily store string and number values in case they cannot
    /// be served directly from [`buf`](Self::buf)
    value_bytes_buf: Vec<u8>,

    peeked: Option<PeekedValue>,
    /// Whether the current array or object is empty, or at top-level whether
    /// at least one value has been consumed already
    is_empty: bool,
    expects_member_name: bool,
    stack: Vec<StackValue>,
    is_string_value_reader_active: bool,

    line: u64,
    column: u64,
    byte_pos: u64,
    json_path: Option<Vec<JsonPathPiece>>,

    reader_settings: ReaderSettings,
}

// TODO: Is there a way to have `R` only optionally implement `Debug`?
impl<R: Read + Debug> Debug for JsonStreamReader<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug_struct = f.debug_struct("JsonStreamReader");
        debug_struct.field("reader", &self.reader);

        if self.reached_eof {
            debug_struct.field("reached_eof", &"true");
        } else {
            debug_struct.field("buf_count", &(self.buf_end_pos - self.buf_pos));
            let buf_content = &self.buf[self.buf_pos..self.buf_end_pos];

            fn limit_str(s: &str, add_ellipsis: bool) -> String {
                match s.char_indices().nth(45) {
                    None => s.to_owned(),
                    Some((index, _)) => {
                        let s = s[..index].to_owned();
                        if add_ellipsis {
                            format!("{s}...")
                        } else {
                            s
                        }
                    }
                }
            }

            match std::str::from_utf8(buf_content) {
                Ok(buf_string) => {
                    debug_struct.field("buf_str", &limit_str(buf_string, true));
                }
                Err(e) => {
                    let prefix_end = e.valid_up_to();
                    let buf_string_prefix = limit_str(
                        std::str::from_utf8(&buf_content[..prefix_end]).unwrap(),
                        // Don't conditionally add ellipsis; code below will always add ellipsis
                        false,
                    );
                    debug_struct.field("buf_str", &format!("{buf_string_prefix}..."));
                    if buf_string_prefix.len() < 15 {
                        // Include some of the invalid bytes which start after the prefix
                        debug_struct.field(
                            "...buf...",
                            &&buf_content[prefix_end..(prefix_end + 30).min(buf_content.len())],
                        );
                    }
                }
            }
        }

        debug_struct
            .field("peeked", &self.peeked)
            .field("is_empty", &self.is_empty)
            .field("expects_member_name", &self.expects_member_name)
            .field("stack", &self.stack)
            .field(
                "is_string_value_reader_active",
                &self.is_string_value_reader_active,
            )
            .field("line", &self.line)
            .field("column", &self.column)
            .field("byte_pos", &self.byte_pos)
            .field("json_path", &self.json_path)
            .field("reader_settings", &self.reader_settings)
            .finish()
    }
}

/// Settings to customize the JSON reader behavior
///
/// These settings are used by [`JsonStreamReader::new_custom`]. To avoid repeating the
/// default values for unchanged settings `..Default::default()` can be used:
/// ```
/// # use struson::reader::ReaderSettings;
/// ReaderSettings {
///     allow_comments: true,
///     // For all other settings use the default
///     ..Default::default()
/// }
/// # ;
/// ```
#[derive(Clone, Debug)]
pub struct ReaderSettings {
    /// Whether to allow comments in the JSON document
    ///
    /// The JSON specification does not allow comments. However, some programs such as
    /// [Visual Studio Code](https://code.visualstudio.com/docs/languages/json#_json-with-comments)
    /// support comments in JSON files.
    ///
    /// When enabled the following two comment variants can be used where the JSON
    /// specification allows whitespace:
    /// - end of line comments: `// ...`\
    ///   The comment spans to the end of the line (next `\r\n`, `\r` or `\n`)
    /// - block comments: `/* ... */`\
    ///   The comment ends at the next `*/` and can include line breaks
    ///
    /// Note that unlike for member names and string values, control characters in the range
    /// `0x00` to `0x1F` (inclusive) are allowed in comments.
    ///
    /// # Examples
    /// ```json
    /// [
    ///     // This is the first value
    ///     1,
    ///     2 /* and this the second */
    /// ]
    /// ```
    pub allow_comments: bool,

    /// Whether to allow an optional trailing comma in JSON arrays or objects
    ///
    /// The JSON specification requires that there must not be a trailing comma (`,`) after the
    /// last item of a JSON array or the last member of a JSON object. However, especially for
    /// 'pretty printed' JSON used with version control software (such as Git) a trailing comma
    /// reduces the diff when adding items or members. For example with trailing comma:
    /// ```json
    /// [
    ///     1,
    /// ]
    /// ```
    /// Adding a `2` to the array is a single line change:
    /// ```json
    /// [
    ///     1,
    ///     2, // <-- only changed line
    /// ]
    /// ```
    /// Whereas without a trailing comma adding a `2` would change two lines: `1` is changed to
    /// `1,` and a new line is added for the `2`.
    ///
    /// **Important:** Since trailing commas are not allowed by the specification, different JSON reader
    /// implementations might handle trailing commas differently. For example some treat them as implicit
    /// `null` value in JSON arrays instead of just ignoring them.
    pub allow_trailing_comma: bool,

    /// Whether to allow multiple top-level values, for example `true [] 1` (3 top-level values)
    ///
    /// Normally a JSON document is expected to contain only a single top-level value, but there
    /// might be use cases where supporting multiple top-level values can be useful.
    ///
    /// It is recommended to separate the values using whitespace (space, tab or line breaks).
    /// If there is no whitespace between the values it is unspecified whether parsing will succeed.
    /// For example the string `truefalse` will likely be rejected and not parsed as JSON values
    /// `true` and `false`.
    pub allow_multiple_top_level: bool,

    /// Whether to track the JSON path while parsing
    ///
    /// The JSON path is reported for [error locations](JsonReaderPosition::path) to make debugging
    /// easier. Disabling path tracking can therefore make troubleshooting malformed JSON data more
    /// difficult, but it might on the other hand improve performance.
    ///
    /// This setting has no effect on the JSON parsing behavior, it only affects the information included
    /// for errors.
    pub track_path: bool,

    /// Whether to restrict which JSON number values are supported
    ///
    /// The JSON specification does not impose any restrictions on the size or precision of JSON numbers.
    /// This means values such as `1e4000` or `1e-4000` are valid JSON numbers. However, parsing such numbers
    /// or performing calculations with them later on can lead to performance issues and can potentially
    /// be exploited for denial of service attacks, especially when they are parsed as arbitrary-precision
    /// "big integer" / "big decimal".
    ///
    /// When enabled exponent values smaller than -99, larger than 99 (e.g. `5e100`) and numbers whose
    /// string representation has more than 100 characters will be rejected and a
    /// [`ReaderError::UnsupportedNumberValue`] is returned. Otherwise, when disabled, all JSON
    /// number values are allowed.
    ///
    /// Note that depending on the use case even these restrictions might not be enough. If necessary
    /// users have to implement additional restrictions themselves, or if possible parse the number as
    /// fixed size integral number such as `u32` instead of "big integer" types.
    pub restrict_number_values: bool,
}

impl Default for ReaderSettings {
    /// Creates the default JSON reader settings
    ///
    /// - comments: disallowed
    /// - trailing comma: disallowed
    /// - multiple top-level values: disallowed
    /// - track JSON path: enabled
    /// - restrict number values: enabled
    ///
    /// These defaults are compliant with the JSON specification.
    fn default() -> Self {
        ReaderSettings {
            allow_comments: false,
            allow_trailing_comma: false,
            allow_multiple_top_level: false,
            track_path: true,
            restrict_number_values: true,
        }
    }
}

// Implementation with public methods
impl<R: Read> JsonStreamReader<R> {
    /// Creates a JSON reader with [default settings](ReaderSettings::default)
    pub fn new(reader: R) -> Self {
        JsonStreamReader::new_custom(reader, ReaderSettings::default())
    }

    /// Creates a JSON reader with custom settings
    ///
    /// The settings can be used to customize which JSON data the reader accepts and to allow
    /// JSON data which is considered invalid by the JSON specification.
    pub fn new_custom(reader: R, reader_settings: ReaderSettings) -> Self {
        let initial_nesting_capacity = 16;
        Self {
            reader,
            buf: [0; READER_BUF_SIZE],
            buf_pos: 0,
            buf_end_pos: 0,
            buf_used_for_bytes_value: false,
            reached_eof: false,
            value_bytes_buf: Vec::with_capacity(INITIAL_VALUE_BYTES_BUF_CAPACITY),
            peeked: None,
            is_empty: true,
            expects_member_name: false,
            stack: Vec::with_capacity(initial_nesting_capacity),
            is_string_value_reader_active: false,
            line: 0,
            column: 0,
            byte_pos: 0,
            json_path: if reader_settings.track_path {
                Some(Vec::with_capacity(initial_nesting_capacity))
            } else {
                None
            },
            reader_settings,
        }
    }

    /// Gets a mutable reference to the underlying reader
    ///
    /// This should only be needed rarely, for advanced use cases only. The reader should not
    /// be used for determining the byte position of the JSON reader, since it might buffer
    /// not yet processed data internally. Instead the [`JsonReaderPosition::data_pos`] of the
    /// [`current_position`](Self::current_position) should be used for that.
    ///
    /// ----
    ///
    /// **🔬 Experimental**\
    /// This method is currently experimental, please provide feedback about how you are using it
    /// [here](https://github.com/Marcono1234/struson/issues/25).
    pub fn reader_mut(&mut self) -> &mut R {
        &mut self.reader
    }
}

// Implementation with error utility methods, and methods for inspecting JSON structure state
impl<R: Read> JsonStreamReader<R> {
    fn create_error_location(&self) -> JsonReaderPosition {
        self.current_position(true)
    }

    fn create_syntax_value_error<T>(
        &self,
        syntax_error_kind: SyntaxErrorKind,
    ) -> Result<T, ReaderError> {
        Err(ReaderError::SyntaxError(JsonSyntaxError {
            kind: syntax_error_kind,
            location: self.create_error_location(),
        }))
    }

    fn is_behind_top_level(&self) -> bool {
        !self.is_empty && self.stack.is_empty()
    }

    fn is_in_array(&self) -> bool {
        self.stack.last().map_or(false, |v| v == &StackValue::Array)
    }

    fn is_in_object(&self) -> bool {
        self.stack
            .last()
            .map_or(false, |v| v == &StackValue::Object)
    }

    fn expects_member_value(&self) -> bool {
        self.is_in_object() && !self.expects_member_name
    }
}

// Implementation with low level byte reading methods
impl<R: Read> JsonStreamReader<R> {
    /// Fills the buffer, starting at `start_pos`
    ///
    /// The [`buf_pos`] is set to `start_pos`. If the end of the input has been
    /// reached `false` is returned.
    fn fill_buffer(&mut self, start_pos: usize) -> Result<bool, ReaderIoError> {
        if self.reached_eof {
            return Ok(false);
        }
        debug_assert!(self.buf_pos >= self.buf_end_pos);
        debug_assert!(start_pos < self.buf.len());

        if self.buf_used_for_bytes_value {
            panic!("Unexpected: Cannot refill buf because it holds a bytes value; report this to the Struson maintainers");
        }

        self.buf_pos = start_pos;
        loop {
            let read_bytes_count = match self.reader.read(&mut self.buf[start_pos..]) {
                Ok(read_bytes_count) => read_bytes_count,
                // Retry if interrupted
                Err(e) if e.kind() == ErrorKind::Interrupted => continue,
                Err(e) => return Err(ReaderIoError(e, self.create_error_location())),
            };
            self.buf_end_pos = start_pos + read_bytes_count;
            break;
        }
        if self.buf_end_pos == start_pos {
            self.reached_eof = true;
            Ok(false)
        } else {
            Ok(true)
        }
    }

    /// Ensures that the buffer is not empty
    ///
    /// If the buffer is currently empty it is refilled start at index 0.
    /// If the end of the input has been reached, `false` is returned.
    /// Otherwise the caller can read the next byte from [`buf`] starting
    /// at [`start_pos`].
    fn ensure_non_empty_buffer(&mut self) -> Result<bool, ReaderIoError> {
        if self.buf_pos < self.buf_end_pos {
            return Ok(true);
        }
        self.fill_buffer(0)
    }

    /// Peeks at the next byte without consuming it
    ///
    /// Returns `None` if the end of the input has been reached.
    fn peek_byte(&mut self) -> Result<Option<u8>, ReaderIoError> {
        if self.ensure_non_empty_buffer()? {
            Ok(Some(self.buf[self.buf_pos]))
        } else {
            Ok(None)
        }
    }

    /// Skips the last byte returned by [`peek_byte`]
    fn skip_peeked_byte(&mut self) {
        debug_assert!(self.buf_pos < self.buf_end_pos);
        self.buf_pos += 1;
    }

    /// Reads the next byte, throwing an error if the end of the
    /// input has been reached
    fn read_byte(&mut self, eof_error_kind: SyntaxErrorKind) -> Result<u8, StringReadingError> {
        if let Some(b) = self.peek_byte()? {
            self.skip_peeked_byte();
            Ok(b)
        } else {
            Err(JsonSyntaxError {
                kind: eof_error_kind,
                location: self.create_error_location(),
            })?
        }
    }
}

// Implementation with whitespace skipping logic
impl<R: Read> JsonStreamReader<R> {
    fn skip_to<P: Fn(u8) -> bool>(
        &mut self,
        stop_predicate: P,
        eof_error_kind: Option<SyntaxErrorKind>,
    ) -> Result<(), ReaderError> {
        let mut has_cr = false;

        while let Some(byte) = self.peek_byte()? {
            if stop_predicate(byte) {
                return Ok(());
            }
            self.skip_peeked_byte();

            match byte {
                b'\n' => {
                    // Count \r\n (Windows line break) as only one line break
                    if !has_cr {
                        self.column = 0;
                        self.line += 1;
                    }
                    self.byte_pos += 1;
                }
                b'\r' => {
                    self.column = 0;
                    self.line += 1;
                    self.byte_pos += 1;
                }
                // Skip ASCII character
                _ if utf8::is_1byte(byte) => {
                    self.column += 1;
                    self.byte_pos += 1;
                }
                _ => {
                    // Validate the UTF-8 data, but ignore it
                    let mut buf = [0_u8; utf8::MAX_BYTES_PER_CHAR];
                    let bytes = self.read_utf8_multibyte(byte, &mut buf)?;
                    self.column += 1;
                    self.byte_pos += bytes.len() as u64;
                }
            }
            // Set this after each iteration so that "\r   \n" is not considered a single line break
            has_cr = byte == b'\r';
        }

        match eof_error_kind {
            None => Ok(()),
            Some(error_kind) => self.create_syntax_value_error(error_kind),
        }
    }

    fn skip_to_line_end(
        &mut self,
        eof_error_kind: Option<SyntaxErrorKind>,
    ) -> Result<(), ReaderError> {
        self.skip_to(|byte| (byte == b'\n') || (byte == b'\r'), eof_error_kind)
        // Don't consume LF or CR, let skip_whitespace handle it
    }

    fn skip_to_block_comment_end(&mut self) -> Result<(), ReaderError> {
        loop {
            self.skip_to(
                |byte| byte == b'*',
                Some(SyntaxErrorKind::BlockCommentNotClosed),
            )?;
            // Consume the '*'
            self.column += 1;
            self.byte_pos += 1;
            self.skip_peeked_byte();

            let byte = match self.peek_byte()? {
                None => {
                    return self.create_syntax_value_error(SyntaxErrorKind::BlockCommentNotClosed)
                }
                Some(byte) => byte,
            };

            if byte == b'/' {
                self.skip_peeked_byte();
                self.column += 1;
                self.byte_pos += 1;
                return Ok(());
            }
            // Otherwise continue loop searching for next '*', but don't consume the peeked
            // byte yet, it might be the next '*', e.g. for "/***/"
        }
    }

    fn skip_whitespace(
        &mut self,
        eof_error_kind: Option<SyntaxErrorKind>,
    ) -> Result<Option<u8>, ReaderError> {
        // Run this in loop because when comment is skipped have to skip whitespace (and comments) again
        loop {
            self.skip_to(
                |byte| {
                    !(
                        // Skip whitespace
                        (byte == b' ') || (byte == b'\t')
                            // Skip line breaks
                            || (byte == b'\n') || (byte == b'\r')
                    )
                },
                None,
            )?;

            let byte = match self.peek_byte()? {
                Some(byte) => byte,
                None => {
                    return eof_error_kind.map_or(Ok(None), |error_kind| {
                        self.create_syntax_value_error(error_kind)
                    });
                }
            };

            if byte == b'/' {
                if !self.reader_settings.allow_comments {
                    return self.create_syntax_value_error(SyntaxErrorKind::CommentsNotEnabled);
                }
                self.skip_peeked_byte();
                self.column += 1;
                self.byte_pos += 1;

                match self.read_byte(SyntaxErrorKind::IncompleteComment)? {
                    b'*' => {
                        self.column += 1;
                        self.byte_pos += 1;
                        self.skip_to_block_comment_end()?;
                    }
                    b'/' => {
                        self.column += 1;
                        self.byte_pos += 1;
                        self.skip_to_line_end(eof_error_kind)?;
                    }
                    _ => {
                        return self.create_syntax_value_error(SyntaxErrorKind::IncompleteComment);
                    }
                }
            } else {
                // Non whitespace or comment, return
                return Ok(Some(byte));
            }
        }
    }

    fn skip_whitespace_no_eof(
        &mut self,
        eof_error_kind: SyntaxErrorKind,
    ) -> Result<u8, ReaderError> {
        // unwrap should be safe, skip_whitespace made sure that EOF has not been reached
        Ok(self.skip_whitespace(Some(eof_error_kind))?.unwrap())
    }
}

// Implementation with peeking (and consumption of literals) logic
impl<R: Read> JsonStreamReader<R> {
    fn verify_value_separator(
        &self,
        byte: u8,
        error_kind: SyntaxErrorKind,
    ) -> Result<(), JsonSyntaxError> {
        match byte {
            // Note: Also includes ':' even though that is not a valid value separator to get more accurate errors
            b',' | b']' | b'}' | b' ' | b'\t' | b'\n' | b'\r' | b'/' | b':' => Ok(()),
            _ => Err(JsonSyntaxError {
                kind: error_kind,
                location: self.create_error_location(),
            }),
        }
    }

    fn consume_literal(&mut self, literal: &str) -> Result<(), ReaderError> {
        for expected_byte in literal.bytes() {
            let byte = self.read_byte(SyntaxErrorKind::InvalidLiteral)?;
            if byte != expected_byte {
                return self.create_syntax_value_error(SyntaxErrorKind::InvalidLiteral);
            }
        }

        // Make sure there are no misleading chars directly afterwards, e.g. "truey"
        if let Some(byte) = self.peek_byte()? {
            self.verify_value_separator(byte, SyntaxErrorKind::TrailingDataAfterLiteral)?;
        }

        // Note: Don't adjust `self.column` yet, is done when peeked value is actually consumed
        Ok(())
    }

    fn peek_internal_optional(&mut self) -> Result<Option<PeekedValue>, ReaderError> {
        if self.is_string_value_reader_active {
            panic!("Incorrect reader usage: Cannot peek when string value reader is active");
        }

        if self.peeked.is_some() {
            return Ok(self.peeked);
        }

        if self.is_behind_top_level() && !self.reader_settings.allow_multiple_top_level {
            panic!("Incorrect reader usage: Cannot peek when top-level value has already been consumed and multiple top-level values are not enabled in settings");
        }
        if self.expects_member_value() {
            // Finish member name which has just been consumed before
            self.after_name()?;
        }

        let byte = self.skip_whitespace(None)?;
        if byte.is_none() {
            return Ok(None);
        }
        let mut byte = byte.unwrap();

        let mut has_trailing_comma = false;
        let mut comma_line = 0;
        let mut comma_column = 0;
        let mut comma_byte_pos = 0;
        let can_have_comma = !self.is_empty && (self.is_in_array() || self.expects_member_name);

        if byte == b',' {
            if !can_have_comma {
                return self.create_syntax_value_error(SyntaxErrorKind::UnexpectedComma);
            }
            self.skip_peeked_byte();
            comma_line = self.line;
            comma_column = self.column;
            comma_byte_pos = self.byte_pos;
            self.column += 1;
            self.byte_pos += 1;
            has_trailing_comma = true;

            byte = self.skip_whitespace_no_eof(SyntaxErrorKind::IncompleteDocument)?;
        }

        let mut advance_reader: bool = true;
        let peeked = if self.expects_member_name {
            match byte {
                b'}' => PeekedValue::ObjectEnd,
                b'"' => PeekedValue::NameStart,
                _ => {
                    return self.create_syntax_value_error(
                        SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
                    );
                }
            }
        } else {
            match byte {
                b'[' => PeekedValue::ArrayStart,
                b']' => {
                    if !self.is_in_array() {
                        return self
                            .create_syntax_value_error(SyntaxErrorKind::UnexpectedClosingBracket);
                    }
                    PeekedValue::ArrayEnd
                }
                b'{' => PeekedValue::ObjectStart,
                b'}' => {
                    return self
                        .create_syntax_value_error(SyntaxErrorKind::UnexpectedClosingBracket);
                }
                b'"' => PeekedValue::StringStart,
                b'-' | b'0'..=b'9' => {
                    // Don't advance yet to preserve first number char for later
                    advance_reader = false;
                    PeekedValue::NumberStart
                }
                b'n' => {
                    self.consume_literal("null")?;
                    advance_reader = false; // consume_literal already advanced reader
                    PeekedValue::Null
                }
                b't' => {
                    self.consume_literal("true")?;
                    advance_reader = false; // consume_literal already advanced reader
                    PeekedValue::BooleanTrue
                }
                b'f' => {
                    self.consume_literal("false")?;
                    advance_reader = false; // consume_literal already advanced reader
                    PeekedValue::BooleanFalse
                }
                b',' => {
                    // Comma has already been handled above
                    return self.create_syntax_value_error(SyntaxErrorKind::UnexpectedComma);
                }
                b':' => {
                    return self.create_syntax_value_error(SyntaxErrorKind::UnexpectedColon);
                }
                _ => {
                    return self.create_syntax_value_error(SyntaxErrorKind::MalformedJson);
                }
            }
        };

        if peeked == PeekedValue::ArrayEnd || peeked == PeekedValue::ObjectEnd {
            if has_trailing_comma && !self.reader_settings.allow_trailing_comma {
                // Report location of comma
                self.line = comma_line;
                self.column = comma_column;
                self.byte_pos = comma_byte_pos;
                return self.create_syntax_value_error(SyntaxErrorKind::TrailingCommaNotEnabled);
            }
        } else if can_have_comma && !has_trailing_comma {
            return self.create_syntax_value_error(SyntaxErrorKind::MissingComma);
        }

        if advance_reader {
            self.skip_peeked_byte();
        }

        self.peeked = Some(peeked);
        Ok(self.peeked)
    }

    fn peek_internal(&mut self) -> Result<PeekedValue, ReaderError> {
        self.peek_internal_optional()?.map_or_else(
            // Handle EOF
            || {
                let eof_as_unexpected_structure =
                    self.is_behind_top_level() && self.reader_settings.allow_multiple_top_level;
                if eof_as_unexpected_structure {
                    Err(ReaderError::UnexpectedStructure {
                        kind: UnexpectedStructureKind::FewerElementsThanExpected,
                        location: self.create_error_location(),
                    })
                } else {
                    self.create_syntax_value_error(SyntaxErrorKind::IncompleteDocument)
                }
            },
            Ok,
        )
    }

    fn map_peeked(&self, peeked: PeekedValue) -> Result<ValueType, ReaderError> {
        Ok(match peeked {
            PeekedValue::ObjectStart => ValueType::Object,
            PeekedValue::ObjectEnd | PeekedValue::NameStart => {
                unreachable!(
                    "peek() should have already panicked when object member name is expected"
                );
            }
            PeekedValue::ArrayStart => ValueType::Array,
            PeekedValue::ArrayEnd => {
                return Err(ReaderError::UnexpectedStructure {
                    kind: UnexpectedStructureKind::FewerElementsThanExpected,
                    location: self.create_error_location(),
                });
            }
            PeekedValue::StringStart => ValueType::String,
            PeekedValue::NumberStart => ValueType::Number,
            PeekedValue::Null => ValueType::Null,
            PeekedValue::BooleanTrue | PeekedValue::BooleanFalse => ValueType::Boolean,
        })
    }

    fn consume_peeked(&mut self) {
        let peeked_length = match self.peeked.take().unwrap() {
            PeekedValue::ObjectStart => 1,
            PeekedValue::ObjectEnd => 1,
            PeekedValue::ArrayStart => 1,
            PeekedValue::ArrayEnd => 1,
            PeekedValue::StringStart | PeekedValue::NameStart => 1, // opening double quote is consumed by peek()
            PeekedValue::NumberStart => 0, // first number char is not consumed during peek()
            PeekedValue::Null => 4,
            PeekedValue::BooleanTrue => 4,
            PeekedValue::BooleanFalse => 5,
        };
        self.column += peeked_length;
        // Peeked value types above consist only of ASCII chars; therefore can treat length as byte count
        self.byte_pos += peeked_length;
    }
}

// Implementation with general value consumption methods
impl<R: Read> JsonStreamReader<R> {
    fn start_expected_value_type(
        &mut self,
        expected: ValueType,
    ) -> Result<PeekedValue, ReaderError> {
        if self.expects_member_name {
            panic!("Incorrect reader usage: Cannot read value when expecting member name");
        }

        let peeked_internal = self.peek_internal()?;
        let peeked = self.map_peeked(peeked_internal)?;

        return if peeked == expected {
            self.consume_peeked();
            Ok(peeked_internal)
        } else {
            Err(ReaderError::UnexpectedValueType {
                expected,
                actual: peeked,
                location: self.create_error_location(),
            })
        };
    }

    fn on_container_end(&mut self) {
        self.stack.pop();
        if let Some(ref mut json_path) = self.json_path {
            json_path.pop();
        }

        self.on_value_end();
    }

    fn on_value_end(&mut self) {
        // Update array path
        if self.is_in_array() {
            if let Some(ref mut json_path) = self.json_path {
                match json_path.last_mut().unwrap() {
                    JsonPathPiece::ArrayItem(index) => *index += 1,
                    _ => unreachable!("Path should be array item"),
                }
            }
        }

        // After value was consumed indicate that object member name is expected next
        if self.is_in_object() {
            self.expects_member_name = true;
        }

        // Enclosing container is not empty since this method call here is processing its child
        self.is_empty = false;
    }
}

// TODO: Maybe try to find a cleaner solution than having this separate trait
trait Utf8MultibyteReader {
    fn read_byte(&mut self, eof_error_kind: SyntaxErrorKind) -> Result<u8, StringReadingError>;

    fn create_error_location(&self) -> JsonReaderPosition;

    fn invalid_utf8_err<'a>(&self) -> Result<&'a [u8], StringReadingError> {
        Err(StringReadingError::IoError(ReaderIoError(
            IoError::new(ErrorKind::InvalidData, "invalid UTF-8 data"),
            self.create_error_location(),
        )))
    }

    /// Reads a UTF-8 char consisting of multiple bytes
    ///
    /// `byte0` is the first byte which has already been read by the caller. `destination_buf` is
    /// used by this method to store all the UTF-8 bytes. A slice of it containing the read bytes
    /// is returned as result; it includes `byte0` as first element.
    fn read_utf8_multibyte<'a>(
        &mut self,
        byte0: u8,
        destination_buf: &'a mut [u8; utf8::MAX_BYTES_PER_CHAR],
    ) -> Result<&'a [u8], StringReadingError> {
        let result_slice: &'a mut [u8];
        let byte1 = self.read_byte(SyntaxErrorKind::IncompleteDocument)?;

        if !utf8::is_continuation(byte1) {
            return self.invalid_utf8_err();
        }

        if utf8::is_2byte_start(byte0) {
            if !utf8::is_valid_2bytes(byte0, byte1) {
                return self.invalid_utf8_err();
            }

            result_slice = &mut destination_buf[..2];
            result_slice[0] = byte0;
            result_slice[1] = byte1;
        } else {
            let byte2 = self.read_byte(SyntaxErrorKind::IncompleteDocument)?;

            if !utf8::is_continuation(byte2) {
                return self.invalid_utf8_err();
            }

            if utf8::is_3byte_start(byte0) {
                if !utf8::is_valid_3bytes(byte0, byte1, byte2) {
                    return self.invalid_utf8_err();
                }

                result_slice = &mut destination_buf[..3];
                result_slice[0] = byte0;
                result_slice[1] = byte1;
                result_slice[2] = byte2;
            } else if utf8::is_4byte_start(byte0) {
                let byte3 = self.read_byte(SyntaxErrorKind::IncompleteDocument)?;

                if !utf8::is_continuation(byte3) {
                    return self.invalid_utf8_err();
                }
                if !utf8::is_valid_4bytes(byte0, byte1, byte2, byte3) {
                    return self.invalid_utf8_err();
                }

                result_slice = &mut destination_buf[..4];
                result_slice[0] = byte0;
                result_slice[1] = byte1;
                result_slice[2] = byte2;
                result_slice[3] = byte3;
            } else {
                return self.invalid_utf8_err();
            }
        }
        Ok(result_slice)
    }
}

// Implementing this directly for JsonStreamReader should be harmless, since the methods of this
// trait implemented below simply delegate to the JsonStreamReader ones
impl<R: Read> Utf8MultibyteReader for JsonStreamReader<R> {
    fn read_byte(&mut self, eof_error_kind: SyntaxErrorKind) -> Result<u8, StringReadingError> {
        self.read_byte(eof_error_kind)
    }

    fn create_error_location(&self) -> JsonReaderPosition {
        self.create_error_location()
    }
}

/// A `char` which was represented by one or two (in case of surrogate pairs)
/// JSON Unicode escape sequences
struct UnicodeEscapeChar {
    c: char,
    /// Number of chars which were part of the escape sequence; does not include the
    /// initial `\u` of the first escape sequence
    consumed_chars_count: u32,
}

// TODO: Maybe try to find a cleaner solution than having this separate trait
trait UnicodeEscapeReader {
    fn read_byte(&mut self, eof_error_kind: SyntaxErrorKind) -> Result<u8, StringReadingError>;

    fn create_error_location(&self) -> JsonReaderPosition;

    fn parse_unicode_escape_hex_digit(&self, digit: u8) -> Result<u32, StringReadingError> {
        match digit {
            b'0'..=b'9' => Ok(u32::from(digit - b'0')),
            b'a'..=b'f' => Ok(u32::from(digit - b'a' + 10)),
            b'A'..=b'F' => Ok(u32::from(digit - b'A' + 10)),
            _ => Err(JsonSyntaxError {
                kind: SyntaxErrorKind::MalformedEscapeSequence,
                location: self.create_error_location(),
            })?,
        }
    }

    fn read_hex_byte(&mut self) -> Result<u32, StringReadingError> {
        let byte = self.read_byte(SyntaxErrorKind::MalformedEscapeSequence)?;
        self.parse_unicode_escape_hex_digit(byte)
    }

    fn read_unicode_escape(&mut self) -> Result<u32, StringReadingError> {
        let d1 = self.read_hex_byte()?;
        let d2 = self.read_hex_byte()?;
        let d3 = self.read_hex_byte()?;
        let d4 = self.read_hex_byte()?;

        Ok(d4 | d3 << 4 | d2 << 8 | d1 << 12)
    }

    /// Reads a Unicode-escaped char
    ///
    /// The caller should have already read the initial `\u` prefix.
    fn read_unicode_escape_char(&mut self) -> Result<UnicodeEscapeChar, StringReadingError> {
        let mut c = self.read_unicode_escape()?;
        // 4 for `XXXX`, the prefix `\u` has already been accounted for by the caller
        let mut consumed_chars_count = 4;

        // Unpaired low surrogate
        if (0xDC00..=0xDFFF).contains(&c) {
            return Err(JsonSyntaxError {
                kind: SyntaxErrorKind::UnpairedSurrogatePairEscapeSequence,
                location: self.create_error_location(),
            })?;
        }
        // If char is high surrogate, expect Unicode-escaped low surrogate
        if (0xD800..=0xDBFF).contains(&c) {
            if !(self.read_byte(SyntaxErrorKind::UnpairedSurrogatePairEscapeSequence)? == b'\\'
                && self.read_byte(SyntaxErrorKind::UnpairedSurrogatePairEscapeSequence)? == b'u')
            {
                return Err(JsonSyntaxError {
                    kind: SyntaxErrorKind::UnpairedSurrogatePairEscapeSequence,
                    location: self.create_error_location(),
                })?;
            }
            let c2 = self.read_unicode_escape()?;
            consumed_chars_count += 6; // \uXXXX
            if !(0xDC00..=0xDFFF).contains(&c2) {
                return Err(JsonSyntaxError {
                    kind: SyntaxErrorKind::UnpairedSurrogatePairEscapeSequence,
                    location: self.create_error_location(),
                })?;
            }

            c = ((c - 0xD800) << 10 | (c2 - 0xDC00)) + 0x10000;
        }

        // unwrap() here should be safe since checks above made sure this is a valid Rust `char`
        let c = char::from_u32(c).unwrap();
        Ok(UnicodeEscapeChar {
            c,
            consumed_chars_count,
        })
    }
}

// Implementing this directly for JsonStreamReader should be harmless, since the methods of this
// trait implemented below simply delegate to the JsonStreamReader ones
impl<R: Read> UnicodeEscapeReader for JsonStreamReader<R> {
    fn read_byte(&mut self, eof_error_kind: SyntaxErrorKind) -> Result<u8, StringReadingError> {
        self.read_byte(eof_error_kind)
    }

    fn create_error_location(&self) -> JsonReaderPosition {
        self.create_error_location()
    }
}

mod bytes_value_reader {
    use std::mem::replace;

    use super::*;

    /// Reader for a 'value' read from the underlying `JsonStreamReader`
    ///
    /// The 'value' can for example be a JSON string value or the string representation of
    /// a JSON number. The main purpose of this struct is to allow retrieving either a
    /// `str` or a `String` later for that value, but hiding the implementation details
    /// of how this value is stored by `JsonStreamReader`.
    /*
     * TODO: Write dedicated unit tests for this which covers corner cases? Or is this covered well enough
     * already by tests for `next_str`, `next_string`, ...
     */
    pub(super) struct BytesValueReader<'j, R: Read> {
        pub(super) json_reader: &'j mut JsonStreamReader<R>,
        /// Whether [`JsonStreamReader::value_bytes_buf`] is used to store the value;
        /// in that case the start of the value might already be in `value_bytes_buf`,
        /// while the remainder might be in [`JsonStreamReader::buf`], with [`buf_value_start`]
        /// being the start and [`JsonStreamReader::buf_pos`] being the end (exclusive)
        is_using_bytes_buf: bool,
        /// Start index of the value (or its remainder) in [`JsonStreamReader::buf`], inclusive;
        /// the end index is [`JsonStreamReader::buf_pos`] (exclusive)
        buf_value_start: usize,
        /// Whether the final byte of the value should be skipped
        ///
        /// This is a special case because unlike for [`skip_previous_byte`] it is not necessary
        /// to save the so far read bytes to [`JsonStreamReader::value_bytes_buf`].
        skip_final_byte: bool,
    }

    /// A bytes value, which is either a borrowed `&[u8]` which can be requested on demand
    /// from the [`JsonStreamReader`], or an owned `Vec<u8>`.
    ///
    /// The caller who created this value must have validated that the collected bytes are
    /// valid UTF-8 data.
    #[derive(Debug)]
    pub(super) enum BytesValue {
        /// A borrowed `&[u8]`
        BytesRef(BytesRefProvider),
        /// An owned `Vec<u8>`
        Vec(Vec<u8>),
    }

    /*
     * == Implementation note ==
     * Cleaner alternative to this would have been to store a reference to the `&[u8]` value
     * in BytesValue, e.g.:
     * ```
     * enum BytesValue<'j> {
     *     Slice(&'j [u8]),
     *     Vec(Vec<u8>),
     * }
     * ```
     * It would then have been transparent where that bytes slice came from (reader buf or bytes value buf),
     * and the method returning the BytesValue could have used the same lifetime for it as for the
     * JsonStreamReader. It would have also allowed to have a `StringValue` enum with a similar structure,
     * containing either a `&'j str` or a `String`.
     *
     * However, this would then have caused issues for users of BytesValue because while they were holding
     * a reference to the BytesValue they were also holding a reference to the JsonStreamReader and therefore
     * the borrow checker would not have allowed any other usage of JsonStreamReader.
     * Therefore this approach delays the access to the `&[u8]` until it is actually requested.
     *
     * Maybe there is a cleaner solution to this though.
     */
    /// Provides access to a `&[u8]` value.
    #[derive(Debug)]
    pub(super) enum BytesRefProvider {
        /// Value is backed by [`JsonStreamReader::buf`]
        ReaderBuf { start: usize, end: usize },
        /// Value is backed by [`JsonStreamReader::value_bytes_buf`]
        BytesValueBuf,
    }

    impl BytesRefProvider {
        fn get_bytes_ref<'j, R: Read>(&self, json_reader: &'j JsonStreamReader<R>) -> &'j [u8] {
            match self {
                BytesRefProvider::ReaderBuf { start, end } => &json_reader.buf[*start..*end],
                BytesRefProvider::BytesValueBuf => &json_reader.value_bytes_buf,
            }
        }

        fn get_str<'j, R: Read>(&self, json_reader: &'j JsonStreamReader<R>) -> &'j str {
            let bytes = self.get_bytes_ref(json_reader);
            // Should be safe; creator of BytesRefProvider should have verified that bytes are valid
            utf8::to_str_unchecked(bytes)
        }
    }

    impl BytesValue {
        /// Gets the read bytes as `String`
        pub(super) fn get_string<R: Read>(self, json_reader: &mut JsonStreamReader<R>) -> String {
            match self {
                BytesValue::BytesRef(b) => {
                    // `get_string` consumes `self` so afterwards value cannot be obtained from `buf` anymore
                    json_reader.buf_used_for_bytes_value = false;
                    b.get_str(json_reader).to_owned()
                }
                // Should be safe; creator of BytesRefProvider should have verified that bytes are valid
                BytesValue::Vec(v) => utf8::to_string_unchecked(v),
            }
        }

        /// Same as [`get_str`](Self::get_str), except that this method does not consume `self`
        pub(super) fn get_str_peek<'j, R: Read>(
            &self,
            json_reader: &'j JsonStreamReader<R>,
        ) -> &'j str {
            match self {
                BytesValue::BytesRef(b) => b.get_str(json_reader),
                // Should be unreachable because when `str` is expected, `true` should have been provided
                // as `requires_borrowed` value, in which case result won't be BytesValue::Vec
                BytesValue::Vec(_) => {
                    panic!("get_str should only be called when `requires_borrowed=true`")
                }
            }
        }

        /// Gets the read bytes as `str`
        ///
        /// Must only be called if the `BytesValue` was obtained from [`BytesValueReader::get_bytes`] being
        /// called with `requires_borrow=true`.
        pub(super) fn get_str<R: Read>(self, json_reader: &mut JsonStreamReader<R>) -> &str {
            // `get_str` consumes `self` so afterwards value cannot be obtained from `buf` anymore
            json_reader.buf_used_for_bytes_value = false;
            self.get_str_peek(json_reader)
        }
    }

    impl<'j, R: Read> BytesValueReader<'j, R> {
        pub(super) fn new(json_reader: &'j mut JsonStreamReader<R>) -> Self {
            let old_buf_start = json_reader.buf_pos;
            // Move buffer content to start of array to make sure complete buffer size is available
            if old_buf_start > 0 {
                let old_buf_end = json_reader.buf_end_pos;
                json_reader.buf.copy_within(old_buf_start..old_buf_end, 0);
                json_reader.buf_pos = 0;
                json_reader.buf_end_pos = old_buf_end - old_buf_start;
            }
            json_reader.value_bytes_buf.clear();
            // Shrink buffer in case it got excessively large during the previous usage
            // TODO: Maybe perform this in `on_value_end` and `after_name` instead
            json_reader
                .value_bytes_buf
                .shrink_to(INITIAL_VALUE_BYTES_BUF_CAPACITY * 2);

            BytesValueReader {
                json_reader,
                is_using_bytes_buf: false,
                buf_value_start: 0,
                skip_final_byte: false,
            }
        }

        /// Peeks at the next byte without consuming it
        ///
        /// To consume the byte afterwards, call [`consume_peeked_byte`].
        /// If the end of the input has been reached and `eof_error_kind` is `None`
        /// `None` is returned. Otherwise an error is returned.
        pub(super) fn peek_byte_optional(
            &mut self,
            eof_error_kind: Option<SyntaxErrorKind>,
        ) -> Result<Option<u8>, StringReadingError> {
            debug_assert!(
                !self.skip_final_byte,
                "Must not read more bytes after final byte was marked as skipped"
            );

            let end_pos = self.json_reader.buf_end_pos;

            if self.json_reader.buf_pos < end_pos {
                let byte = self.json_reader.buf[self.json_reader.buf_pos];
                Ok(Some(byte))
            }
            // Else check if can / have to start at index 0 of `json_reader.buf`
            else if self.is_using_bytes_buf
                || self.json_reader.buf_pos >= self.json_reader.buf.len()
            {
                // Save all bytes which should be kept
                if self.buf_value_start < end_pos {
                    let bytes = &self.json_reader.buf[self.buf_value_start..end_pos];
                    self.json_reader.value_bytes_buf.extend_from_slice(bytes);
                    self.is_using_bytes_buf = true;
                }

                self.buf_value_start = 0;

                if self.json_reader.fill_buffer(0)? {
                    Ok(Some(self.json_reader.buf[0]))
                } else if let Some(eof_error_kind) = eof_error_kind {
                    Err(JsonSyntaxError {
                        kind: eof_error_kind,
                        location: self.json_reader.create_error_location(),
                    })?
                } else {
                    Ok(None)
                }
            }
            // Else continue filling `json_reader.buf` behind previously read data
            else {
                #[allow(clippy::collapsible_else_if)]
                if self.json_reader.fill_buffer(end_pos)? {
                    Ok(Some(self.json_reader.buf[end_pos]))
                } else if let Some(eof_error_kind) = eof_error_kind {
                    Err(JsonSyntaxError {
                        kind: eof_error_kind,
                        location: self.json_reader.create_error_location(),
                    })?
                } else {
                    Ok(None)
                }
            }
        }

        /// Reads the next byte
        pub(super) fn read_byte(
            &mut self,
            eof_error_kind: SyntaxErrorKind,
        ) -> Result<u8, StringReadingError> {
            let byte = self
                .peek_byte_optional(Some(eof_error_kind))
                .map(|b| b.unwrap())?;
            self.consume_peeked_byte();
            Ok(byte)
        }

        /// Consumes the previous peeked byte which has just been peeked at using [`peek_byte_optional`]
        #[inline(always)]
        pub(super) fn consume_peeked_byte(&mut self) {
            self.json_reader.buf_pos += 1;
        }

        /// Skips the previous byte which has just been read using [`read_byte`]
        pub(super) fn skip_previous_byte(&mut self) {
            debug_assert!(
                !self.skip_final_byte,
                "Cannot skip after byte has already been marked as skipped final byte"
            );

            // End position (exclusive) of the value; `buf_pos` is the index of the next not yet consumed byte
            let end_pos = self.json_reader.buf_pos;

            // If no bytes have been kept so far, can just increase index
            if self.buf_value_start + 1 == end_pos {
                self.buf_value_start += 1;
            }
            // Otherwise need to save the previous part of the value
            else {
                // `end_pos - 1` because the current byte should be skipped
                let bytes = &self.json_reader.buf[self.buf_value_start..end_pos - 1];
                self.json_reader.value_bytes_buf.extend_from_slice(bytes);
                self.is_using_bytes_buf = true;
                self.buf_value_start = end_pos;
            }
        }

        /// Skips the final byte of the value, which has just been read using [`read_byte`]. Afterwards no
        /// further bytes may be read and [`push_bytes`] should be called.
        /// This method is intended for values where the final delimiter has been read, which should not
        /// be part of the value, for example the closing `"` of a string.
        pub(super) fn skip_final_byte(&mut self) {
            self.skip_final_byte = true;
        }

        /// Pushes bytes into the value buffer
        ///
        /// This can be used in combination with [`skip_previous_byte`] to replace bytes
        /// in the value, by first skipping the original bytes and then pushing a replacement,
        /// for example for JSON string escape sequences.
        pub(super) fn push_bytes(&mut self, bytes: &[u8]) {
            let end_pos = self.json_reader.buf_pos;
            if self.buf_value_start < end_pos {
                // Push remainder into buffer
                self.json_reader
                    .value_bytes_buf
                    .extend_from_slice(&self.json_reader.buf[self.buf_value_start..end_pos]);
                self.buf_value_start = end_pos;
            }

            self.is_using_bytes_buf = true;
            self.json_reader.value_bytes_buf.extend_from_slice(bytes);
        }

        /// Gets the final bytes value. Must be called at most once.
        /*
         * Ideally would use `self` instead of `&mut self` to prevent calling this method multiple times
         * by accident, but in some cases need access to `json_reader` from field of this struct afterwards
         * to obtain string value from `BytesValue`; therefore for now keep this as `&mut self`
         */
        pub(super) fn get_bytes(&mut self, requires_borrowed: bool) -> BytesValue {
            let mut end_pos = self.json_reader.buf_pos;
            if self.skip_final_byte {
                end_pos -= 1;
            }

            if self.is_using_bytes_buf {
                // Push remainder into buffer
                self.json_reader
                    .value_bytes_buf
                    .extend_from_slice(&self.json_reader.buf[self.buf_value_start..end_pos]);

                if requires_borrowed {
                    // Indicate that value is in `value_bytes_buf`
                    BytesValue::BytesRef(BytesRefProvider::BytesValueBuf)
                } else {
                    let bytes = replace(
                        &mut self.json_reader.value_bytes_buf,
                        Vec::with_capacity(INITIAL_VALUE_BYTES_BUF_CAPACITY),
                    );
                    BytesValue::Vec(bytes)
                }
            } else {
                // Indicate that `buf` contains bytes value, to prevent accidental modification
                debug_assert!(!self.json_reader.buf_used_for_bytes_value);
                self.json_reader.buf_used_for_bytes_value = true;

                BytesValue::BytesRef(BytesRefProvider::ReaderBuf {
                    start: self.buf_value_start,
                    end: end_pos,
                })
            }
        }
    }

    // 'newtype pattern' to avoid leaking `read_byte` implementation directly for BytesValueReader (and to avoid ambiguity)
    pub(super) struct AsUtf8MultibyteReader<'a, 'j, R: Read>(
        pub(super) &'a mut BytesValueReader<'j, R>,
    );
    impl<R: Read> Utf8MultibyteReader for AsUtf8MultibyteReader<'_, '_, R> {
        fn read_byte(&mut self, eof_error_kind: SyntaxErrorKind) -> Result<u8, StringReadingError> {
            // Note: Don't need to skip byte because it will be part of the final value
            self.0.read_byte(eof_error_kind)
        }

        fn create_error_location(&self) -> JsonReaderPosition {
            self.0.json_reader.create_error_location()
        }
    }

    // 'newtype pattern' to avoid leaking `read_byte` implementation directly for BytesValueReader (and to avoid ambiguity)
    pub(super) struct AsUnicodeEscapeReader<'a, 'j, R: Read>(
        pub(super) &'a mut BytesValueReader<'j, R>,
    );
    impl<R: Read> UnicodeEscapeReader for AsUnicodeEscapeReader<'_, '_, R> {
        fn read_byte(&mut self, eof_error_kind: SyntaxErrorKind) -> Result<u8, StringReadingError> {
            let byte = self.0.read_byte(eof_error_kind)?;
            // Skip byte which is part of escape sequence; should not be in the final value
            self.0.skip_previous_byte();
            Ok(byte)
        }

        fn create_error_location(&self) -> JsonReaderPosition {
            self.0.json_reader.create_error_location()
        }
    }
}

// Implementation with string and object member name reading methods
impl<R: Read> JsonStreamReader<R> {
    /// Reads the next character of a member name or string value
    ///
    /// If it is an unescaped `"` returns true. Otherwise passes the bytes of the char
    /// (1 - 4 bytes) to the given consumer and returns false.
    fn read_string_bytes<C: FnMut(u8)>(
        &mut self,
        consumer: &mut C,
    ) -> Result<bool, StringReadingError> {
        let byte = self.read_byte(SyntaxErrorKind::IncompleteDocument)?;

        let mut reached_end = false;
        let mut consumed_chars_count = 1;
        let mut consumed_bytes_count = 1;
        match byte {
            // Read escape sequence
            b'\\' => {
                let byte = self.read_byte(SyntaxErrorKind::MalformedEscapeSequence)?;
                consumed_chars_count += 1;
                consumed_bytes_count += 1;

                match byte {
                    b'"' | b'\\' | b'/' => consumer(byte),
                    b'b' => consumer(0x08),
                    b'f' => consumer(0x0C),
                    b'n' => consumer(b'\n'),
                    b'r' => consumer(b'\r'),
                    b't' => consumer(b'\t'),
                    b'u' => {
                        let UnicodeEscapeChar {
                            c,
                            consumed_chars_count: escape_consumed_chars_count,
                        } = self.read_unicode_escape_char()?;
                        consumed_chars_count += escape_consumed_chars_count as u64;
                        // Treat as byte count because Unicode escape only uses single byte ASCII chars
                        consumed_bytes_count += escape_consumed_chars_count as u64;

                        let mut char_encode_buf = [0; utf8::MAX_BYTES_PER_CHAR];
                        let encoded_char = c.encode_utf8(&mut char_encode_buf);
                        for b in encoded_char.as_bytes() {
                            consumer(*b);
                        }
                    }
                    _ => {
                        return Err(JsonSyntaxError {
                            kind: SyntaxErrorKind::UnknownEscapeSequence,
                            location: self.create_error_location(),
                        })?
                    }
                }
            }
            b'"' => {
                reached_end = true;
            }
            // Control characters must be written as Unicode escape
            0x00..=0x1F => {
                return Err(JsonSyntaxError {
                    kind: SyntaxErrorKind::NotEscapedControlCharacter,
                    location: self.create_error_location(),
                })?;
            }
            // Non-control ASCII characters
            0x20..=0x7F => {
                consumer(byte);
            }
            // Read and validate multibyte UTF-8 data
            _ => {
                let mut buf = [0_u8; utf8::MAX_BYTES_PER_CHAR];
                let bytes = self.read_utf8_multibyte(byte, &mut buf)?;
                for b in bytes {
                    consumer(*b);
                }
                // - 1 because `byte0` has already been counted at start of `match`
                consumed_bytes_count += bytes.len() as u64 - 1;
            }
        }

        // Update location afterwards, so in case of error, start position of escape sequence or multi-byte UTF-8 char is reported
        self.column += consumed_chars_count;
        self.byte_pos += consumed_bytes_count;
        Ok(reached_end)
    }

    fn read_all_string_bytes<C: FnMut(u8)>(
        &mut self,
        consumer: &mut C,
    ) -> Result<(), StringReadingError> {
        loop {
            let reached_end = self.read_string_bytes(consumer)?;
            if reached_end {
                return Ok(());
            }
        }
    }

    fn skip_all_string_bytes(&mut self) -> Result<(), StringReadingError> {
        self.read_all_string_bytes(&mut |_| {})
    }

    /// Reads a JSON string value (either a JSON string or a member name) and returns a `BytesValue`
    /// for access to it. The `BytesValue` is guaranteed to refer to valid UTF-8 bytes.
    ///
    /// `requires_borrowed` indicates whether the caller requires obtaining the string value
    /// as `str` later by calling [`BytesValue::get_str`].
    fn read_string(&mut self, requires_borrowed: bool) -> Result<BytesValue, StringReadingError> {
        let mut bytes_reader = BytesValueReader::new(self);
        let read_bytes: BytesValue;

        loop {
            let byte = bytes_reader.read_byte(SyntaxErrorKind::IncompleteDocument)?;
            match byte {
                // Read escape sequence
                b'\\' => {
                    // Exclude the '\' from the value
                    bytes_reader.skip_previous_byte();
                    let byte = bytes_reader.read_byte(SyntaxErrorKind::MalformedEscapeSequence)?;

                    match byte {
                        b'"' | b'\\' | b'/' => {} // do nothing, keep the literal char as part of the `bytes_reader` value
                        b'b' => {
                            // Skip the 'b' and instead push the represented char
                            bytes_reader.skip_previous_byte();
                            bytes_reader.push_bytes(&[0x08]);
                        }
                        b'f' => {
                            // Skip the 'f' and instead push the represented char
                            bytes_reader.skip_previous_byte();
                            bytes_reader.push_bytes(&[0x0C]);
                        }
                        b'n' => {
                            // Skip the 'n' and instead push the represented char
                            bytes_reader.skip_previous_byte();
                            bytes_reader.push_bytes(&[b'\n']);
                        }
                        b'r' => {
                            // Skip the 'r' and instead push the represented char
                            bytes_reader.skip_previous_byte();
                            bytes_reader.push_bytes(&[b'\r']);
                        }
                        b't' => {
                            // Skip the 't' and instead push the represented char
                            bytes_reader.skip_previous_byte();
                            bytes_reader.push_bytes(&[b'\t']);
                        }
                        b'u' => {
                            // Skip the 'u'
                            bytes_reader.skip_previous_byte();

                            let UnicodeEscapeChar {
                                c,
                                consumed_chars_count,
                            } = AsUnicodeEscapeReader(&mut bytes_reader)
                                .read_unicode_escape_char()?;
                            bytes_reader.json_reader.column += consumed_chars_count as u64;
                            // Treat as byte count because Unicode escape only uses single byte ASCII chars
                            bytes_reader.json_reader.byte_pos += consumed_chars_count as u64;
                            let mut char_encode_buf = [0; utf8::MAX_BYTES_PER_CHAR];
                            let encoded_char = c.encode_utf8(&mut char_encode_buf);
                            bytes_reader.push_bytes(encoded_char.as_bytes());
                        }
                        _ => {
                            return Err(JsonSyntaxError {
                                kind: SyntaxErrorKind::UnknownEscapeSequence,
                                location: bytes_reader.json_reader.create_error_location(),
                            })?
                        }
                    }
                    // After escape sequence was successfully read, update location information;
                    // otherwise error message would point at the middle of escape sequence
                    bytes_reader.json_reader.column += 2;
                    bytes_reader.json_reader.byte_pos += 2;
                }
                b'"' => {
                    bytes_reader.json_reader.column += 1;
                    bytes_reader.json_reader.byte_pos += 1;
                    // Don't include the '"' in the value
                    bytes_reader.skip_final_byte();
                    read_bytes = bytes_reader.get_bytes(requires_borrowed);
                    break;
                }
                // Control characters must be written as Unicode escape
                0x00..=0x1F => {
                    return Err(JsonSyntaxError {
                        kind: SyntaxErrorKind::NotEscapedControlCharacter,
                        location: bytes_reader.json_reader.create_error_location(),
                    })?;
                }
                // Non-control ASCII characters
                0x20..=0x7F => {
                    bytes_reader.json_reader.column += 1;
                    bytes_reader.json_reader.byte_pos += 1;
                    // Note: bytes_reader will keep the byte in the final value because it is not skipped here
                }
                // Read and validate multibyte UTF-8 data
                // Note: Technically this could be omitted, ASCII and multibyte UTF-8 could be treated the same
                // and UTF-8 validation from Rust standard library could be used, however, then it would not be easily
                // possible anymore to track the character location for error messages because it would not be clear
                // how many bytes are part of a character
                _ => {
                    let mut buf = [0_u8; utf8::MAX_BYTES_PER_CHAR];
                    // Ignore bytes here, bytes_reader will keep the bytes in the final value because they are not skipped here
                    let bytes = AsUtf8MultibyteReader(&mut bytes_reader)
                        .read_utf8_multibyte(byte, &mut buf)?;
                    bytes_reader.json_reader.column += 1;
                    bytes_reader.json_reader.byte_pos += bytes.len() as u64;
                }
            }
        }

        // Code above manually performed UTF-8 validation, `read_bytes` should be safe to use for obtaining strings
        Ok(read_bytes)
    }

    // Note: This is split into `before_name` and `after_name` to allow both `next_name` and `skip_name`
    // to reuse this code
    fn before_name(&mut self) -> Result<(), ReaderError> {
        if !self.expects_member_name {
            panic!("Incorrect reader usage: Cannot consume member name when not expecting it");
        }
        if self.is_string_value_reader_active {
            panic!("Incorrect reader usage: Cannot consume member name when string value reader is active");
        }

        if !self.has_next()? {
            return Err(ReaderError::UnexpectedStructure {
                kind: UnexpectedStructureKind::FewerElementsThanExpected,
                location: self.create_error_location(),
            });
        }

        self.expects_member_name = false;
        // `has_next` call above peeked at start of member name; consume opening double quote here now
        self.consume_peeked();
        Ok(())
    }

    fn after_name(&mut self) -> Result<(), ReaderError> {
        let byte = self.skip_whitespace_no_eof(SyntaxErrorKind::MissingColon)?;
        return if byte == b':' {
            self.skip_peeked_byte();
            self.column += 1;
            self.byte_pos += 1;
            Ok(())
        } else {
            self.create_syntax_value_error(SyntaxErrorKind::MissingColon)
        };
    }
}

// Implementation for number reading
trait NumberBytesReader<T, E>: NumberBytesProvider<E> {
    /// Gets the number of consumed bytes
    fn get_consumed_bytes_count(&self) -> u32;
    /// Returns whether this reader restricts the read number (length or exponent)
    fn restricts_number(&self) -> bool;
    /// If [`restricts_number`] returns true, gets the number string for error reporting in case
    /// it does not match the restrictions.
    fn get_number_string_for_error(self) -> String;
    fn get_result(self) -> T;
}

// Using macro here to avoid issues with borrow checker; probably not the cleanest solution
// TODO: Try to find a cleaner solution without using macro?
macro_rules! collect_next_number_bytes {
    ( |$self:ident| $reader_creator:expr ) => {{
        $self.start_expected_value_type(ValueType::Number)?;

        // unwrap() is safe because start_expected_value_type already peeked at first number byte
        let first_byte = $self.peek_byte()?.unwrap();
        let mut reader = $reader_creator;
        let number_result = consume_json_number(&mut reader, first_byte)?;
        let exponent_digits_count = match number_result {
            None => return $self.create_syntax_value_error(SyntaxErrorKind::MalformedNumber),
            Some(exponent_digits_count) => exponent_digits_count,
        };

        let consumed_bytes = reader.get_consumed_bytes_count();
        if reader.restricts_number() {
            // >= e100, <= e-100 or complete number longer than 100 chars
            if exponent_digits_count > 2 || consumed_bytes > 100 {
                return Err(ReaderError::UnsupportedNumberValue {
                    number: reader.get_number_string_for_error(),
                    location: $self.create_error_location(),
                });
            }
        }

        let result = reader.get_result();
        $self.column += consumed_bytes as u64;
        $self.byte_pos += consumed_bytes as u64;
        // Make sure there are no misleading chars directly afterwards, e.g. "123f"
        if let Some(byte) = $self.peek_byte()? {
            $self.verify_value_separator(byte, SyntaxErrorKind::TrailingDataAfterNumber)?
        }

        $self.on_value_end();
        result
    }};
}

impl<R: Read> JsonStreamReader<R> {
    /// Reads a JSON number and returns a `BytesValue` for access to its string representation.
    /// The `BytesValue` is guaranteed to refer to valid UTF-8 bytes.
    ///
    /// `requires_borrowed` indicates whether the caller requires obtaining the string representation
    /// as `str` later by calling [`BytesValue::get_str`].
    fn read_number_bytes(&mut self, requires_borrowed: bool) -> Result<BytesValue, ReaderError> {
        let restrict_number = self.reader_settings.restrict_number_values;

        Ok(collect_next_number_bytes!(|self| NumberBytesValueReader {
            reader: BytesValueReader::new(self),
            consumed_bytes: 0,
            restrict_number,
            requires_borrowed_result: requires_borrowed,
        }))
    }
}

struct NumberBytesValueReader<'j, R: Read> {
    reader: BytesValueReader<'j, R>,
    consumed_bytes: u32,
    restrict_number: bool,
    requires_borrowed_result: bool,
}
impl<R: Read> NumberBytesProvider<ReaderError> for NumberBytesValueReader<'_, R> {
    fn consume_current_peek_next(&mut self) -> Result<Option<u8>, ReaderError> {
        // Note: The first byte was not actually read by `BytesValueReader`, instead it was peeked by creator
        // of NumberBytesValueReader. However, consume it here to include it in the final value.
        self.reader.consume_peeked_byte();
        self.consumed_bytes += 1;
        Ok(self.reader.peek_byte_optional(None)?)
    }
}
impl<R: Read> NumberBytesReader<BytesValue, ReaderError> for NumberBytesValueReader<'_, R> {
    fn get_consumed_bytes_count(&self) -> u32 {
        self.consumed_bytes
    }

    fn restricts_number(&self) -> bool {
        self.restrict_number
    }

    fn get_number_string_for_error(mut self) -> String {
        self.reader
            // No UTF-8 checks are needed because JSON number consists only of ASCII chars
            .get_bytes(false)
            .get_string(self.reader.json_reader)
    }

    fn get_result(mut self) -> BytesValue {
        // No UTF-8 checks are needed because JSON number consists only of ASCII chars
        self.reader.get_bytes(self.requires_borrowed_result)
    }
}

struct SkippingNumberBytesReader<'j, R: Read> {
    json_reader: &'j mut JsonStreamReader<R>,
    consumed_bytes: u32,
}
impl<R: Read> NumberBytesProvider<ReaderIoError> for SkippingNumberBytesReader<'_, R> {
    fn consume_current_peek_next(&mut self) -> Result<Option<u8>, ReaderIoError> {
        // Should not fail since last peek_byte() succeeded
        self.json_reader.skip_peeked_byte();
        self.consumed_bytes += 1;
        self.json_reader.peek_byte()
    }
}
impl<R: Read> NumberBytesReader<(), ReaderIoError> for SkippingNumberBytesReader<'_, R> {
    fn get_consumed_bytes_count(&self) -> u32 {
        self.consumed_bytes
    }

    fn restricts_number(&self) -> bool {
        // Don't restrict number values while skipping
        false
    }

    fn get_number_string_for_error(self) -> String {
        unreachable!("Should not be called since restricts_number() returns false")
    }

    fn get_result(self) {}
}

impl<R: Read> JsonReader for JsonStreamReader<R> {
    fn peek(&mut self) -> Result<ValueType, ReaderError> {
        if self.expects_member_name {
            panic!("Incorrect reader usage: Cannot peek value when expecting member name");
        }
        let peeked = self.peek_internal()?;
        self.map_peeked(peeked)
    }

    fn begin_array(&mut self) -> Result<(), ReaderError> {
        self.start_expected_value_type(ValueType::Array)?;
        self.stack.push(StackValue::Array);

        if let Some(ref mut json_path) = self.json_path {
            json_path.push(JsonPathPiece::ArrayItem(0));
        }

        // Clear this because it is only relevant for objects; will be restored when entering parent object (if any) again
        self.expects_member_name = false;
        self.is_empty = true;
        Ok(())
    }

    fn end_array(&mut self) -> Result<(), ReaderError> {
        if !self.is_in_array() {
            panic!("Incorrect reader usage: Cannot end array when not inside array");
        }
        let peeked = self.peek_internal()?;
        if peeked != PeekedValue::ArrayEnd {
            return Err(ReaderError::UnexpectedStructure {
                kind: UnexpectedStructureKind::MoreElementsThanExpected,
                location: self.create_error_location(),
            });
        }
        self.consume_peeked();
        self.on_container_end();
        Ok(())
    }

    fn begin_object(&mut self) -> Result<(), ReaderError> {
        self.start_expected_value_type(ValueType::Object)?;
        self.stack.push(StackValue::Object);

        if let Some(ref mut json_path) = self.json_path {
            // Push a placeholder which is replaced once the name of the first member is read
            // Important: When changing this placeholder in the future also have to update documentation mentioning to it
            json_path.push(JsonPathPiece::ObjectMember("<?>".to_owned()));
        }

        self.is_empty = true;
        self.expects_member_name = true;
        Ok(())
    }

    fn next_name_owned(&mut self) -> Result<String, ReaderError> {
        self.before_name()?;

        let name = self.read_string(false)?.get_string(self);

        if let Some(ref mut json_path) = self.json_path {
            match json_path.last_mut().unwrap() {
                JsonPathPiece::ObjectMember(path_name) => *path_name = name.clone(),
                _ => unreachable!("Path should be object member"),
            }
        }
        Ok(name)
        // Consuming `:` after name is delayed until member value is consumed
    }

    fn next_name(&mut self) -> Result<&str, ReaderError> {
        self.before_name()?;

        let name_bytes = self.read_string(true)?;

        if self.json_path.is_some() {
            // TODO: Not ideal that this causes `std::str::from_utf8` to be called twice, once here and once
            // for return value; not sure though if this can be solved
            let name = name_bytes.get_str_peek(self).to_owned();
            // `unwrap` call here is safe due to `is_some` check above (cannot easily rewrite this because there
            // would be two mutable borrows of `self` then at the same time)
            match self.json_path.as_mut().unwrap().last_mut().unwrap() {
                JsonPathPiece::ObjectMember(path_name) => *path_name = name,
                _ => unreachable!("Path should be object member"),
            }
        }
        Ok(name_bytes.get_str(self))
        // Consuming `:` after name is delayed until member value is consumed; otherwise if it was done
        // here it might refill the reader buffer and accidentally overwrite the value of `name_bytes`
    }

    fn end_object(&mut self) -> Result<(), ReaderError> {
        if !self.is_in_object() {
            panic!("Incorrect reader usage: Cannot end object when not inside object");
        }
        if self.expects_member_value() {
            panic!("Incorrect reader usage: Cannot end object when member value is expected");
        }
        let peeked = self.peek_internal()?;
        if peeked != PeekedValue::ObjectEnd {
            return Err(ReaderError::UnexpectedStructure {
                kind: UnexpectedStructureKind::MoreElementsThanExpected,
                location: self.create_error_location(),
            });
        }
        self.consume_peeked();
        // Clear expects_member_name in case current container is now an array; on_container_end() call
        // below (respectively on_value_end() called by it) will set expects_member_name again if
        // enclosing container is an object
        self.expects_member_name = false;
        self.on_container_end();
        Ok(())
    }

    fn next_bool(&mut self) -> Result<bool, ReaderError> {
        let result = Ok(match self.start_expected_value_type(ValueType::Boolean)? {
            PeekedValue::BooleanTrue => true,
            PeekedValue::BooleanFalse => false,
            // Call to start_expected_value_type should have verified type
            _ => unreachable!("Peeked value is not a boolean"),
        });
        self.on_value_end();
        result
    }

    fn next_null(&mut self) -> Result<(), ReaderError> {
        self.start_expected_value_type(ValueType::Null)?;
        self.on_value_end();
        Ok(())
    }

    fn has_next(&mut self) -> Result<bool, ReaderError> {
        if self.expects_member_value() {
            panic!("Incorrect reader usage: Cannot check for next element when member value is expected");
        }

        let peeked: PeekedValue;
        if self.stack.is_empty() {
            if self.is_empty {
                panic!("Incorrect reader usage: Cannot check for next element when top-level value has not been started");
            } else if !self.reader_settings.allow_multiple_top_level {
                panic!("Incorrect reader usage: Cannot check for multiple top-level values when not enabled in the reader settings");
            } else {
                peeked = match self.peek_internal_optional()? {
                    None => return Ok(false),
                    Some(p) => p,
                }
            }
        } else {
            peeked = self.peek_internal()?;
        }
        debug_assert!(
            !self.expects_member_name
                || peeked == PeekedValue::NameStart
                || peeked == PeekedValue::ObjectEnd
        );

        Ok((peeked != PeekedValue::ArrayEnd) && (peeked != PeekedValue::ObjectEnd))
    }

    fn skip_name(&mut self) -> Result<(), ReaderError> {
        self.before_name()?;

        if self.json_path.is_some() {
            // Similar to `next_name` implementation, except that `name` can directly be moved to
            // json_path piece instead of having to be cloned
            let name = self.read_string(false)?.get_string(self);

            // `unwrap` call here is safe due to `is_some` check above (cannot easily rewrite this because there
            // would be two mutable borrows of `self` then at the same time)
            match self.json_path.as_mut().unwrap().last_mut().unwrap() {
                JsonPathPiece::ObjectMember(path_name) => *path_name = name,
                _ => unreachable!("Path should be object member"),
            }
        } else {
            self.skip_all_string_bytes()?;
        }
        Ok(())
        // Consuming `:` after name is delayed until member value is consumed
    }

    fn skip_value(&mut self) -> Result<(), ReaderError> {
        if self.expects_member_name {
            panic!("Incorrect reader usage: Cannot skip value when expecting member name");
        }

        let mut depth: u32 = 0;
        loop {
            if depth > 0 && !self.has_next()? {
                if self.is_in_array() {
                    self.end_array()?;
                } else {
                    self.end_object()?;
                }
                depth -= 1;
            } else {
                if self.expects_member_name {
                    self.skip_name()?;
                }

                match self.peek()? {
                    ValueType::Array => {
                        self.begin_array()?;
                        depth += 1;
                    }
                    ValueType::Object => {
                        self.begin_object()?;
                        depth += 1;
                    }
                    ValueType::String => {
                        self.start_expected_value_type(ValueType::String)?;
                        self.skip_all_string_bytes()?;
                        self.on_value_end();
                    }
                    ValueType::Number => {
                        collect_next_number_bytes!(|self| SkippingNumberBytesReader {
                            json_reader: self,
                            consumed_bytes: 0,
                        });
                    }
                    ValueType::Boolean => {
                        self.next_bool()?;
                    }
                    ValueType::Null => {
                        self.next_null()?;
                    }
                }
            }

            if depth == 0 {
                break;
            }
        }

        Ok(())
    }

    fn next_string(&mut self) -> Result<String, ReaderError> {
        self.start_expected_value_type(ValueType::String)?;
        let result = self.read_string(false)?.get_string(self);
        self.on_value_end();
        Ok(result)
    }

    fn next_str(&mut self) -> Result<&str, ReaderError> {
        self.start_expected_value_type(ValueType::String)?;
        let str_bytes = self.read_string(true)?;
        self.on_value_end();
        Ok(str_bytes.get_str(self))
    }

    fn next_string_reader(&mut self) -> Result<Box<dyn Read + '_>, ReaderError> {
        self.start_expected_value_type(ValueType::String)?;
        self.is_string_value_reader_active = true;
        Ok(Box::new(StringValueReader {
            json_reader: self,
            utf8_buf: [0; STRING_VALUE_READER_BUF_SIZE],
            utf8_start_pos: 0,
            utf8_count: 0,
            reached_end: false,
            error: None,
        }))
    }

    fn next_number_as_string(&mut self) -> Result<String, ReaderError> {
        self.read_number_bytes(false).map(|b| b.get_string(self))
    }

    fn next_number_as_str(&mut self) -> Result<&str, ReaderError> {
        self.read_number_bytes(true).map(|b| b.get_str(self))
    }

    #[cfg(feature = "serde")]
    fn deserialize_next<'de, D: serde::de::Deserialize<'de>>(
        &mut self,
    ) -> Result<D, crate::serde::DeserializerError> {
        // TODO: Provide this as default implementation? Remove implementation in custom_json_reader test then;
        // does not seem to be possible though because Self would have to be guaranteed to be `Sized`?
        // not sure if that should be enforced for the JsonReader trait

        // peek here to fail fast if reader is currently not expecting a value
        self.peek()?;
        let mut deserializer = crate::serde::JsonReaderDeserializer::new(self);
        D::deserialize(&mut deserializer)
        // TODO: Verify that value was properly deserialized (only single value; no incomplete array or object)
        //       might not be necessary because Serde's Deserializer API enforces this by consuming `self`, and
        //       JsonReaderDeserializer makes sure JSON arrays and objects are read completely
    }

    fn skip_to_top_level(&mut self) -> Result<(), ReaderError> {
        if self.is_string_value_reader_active {
            panic!("Incorrect reader usage: Cannot skip to top level when string value reader is active");
        }

        // Handle expected member value separately because has_next() calls below are not allowed when
        // member value is expected
        if self.expects_member_value() {
            self.skip_value()?;
        }

        while let Some(value_type) = self.stack.last() {
            match value_type {
                StackValue::Array => {
                    while self.has_next()? {
                        self.skip_value()?;
                    }
                    self.end_array()?;
                }
                StackValue::Object => {
                    while self.has_next()? {
                        self.skip_name()?;
                        self.skip_value()?;
                    }
                    self.end_object()?;
                }
            }
        }
        Ok(())
    }

    fn transfer_to<W: JsonWriter>(&mut self, json_writer: &mut W) -> Result<(), TransferError> {
        if self.expects_member_name {
            panic!("Incorrect reader usage: Cannot transfer value when expecting member name");
        }

        let mut depth: u32 = 0;
        loop {
            if depth > 0 && !self.has_next()? {
                if self.is_in_array() {
                    self.end_array()?;
                    json_writer.end_array()?;
                } else {
                    self.end_object()?;
                    json_writer.end_object()?;
                }
                depth -= 1;
            } else {
                if self.expects_member_name {
                    let name = self.next_name()?;
                    json_writer.name(name)?;
                }

                match self.peek()? {
                    ValueType::Array => {
                        self.begin_array()?;
                        json_writer.begin_array()?;
                        depth += 1;
                    }
                    ValueType::Object => {
                        self.begin_object()?;
                        json_writer.begin_object()?;
                        depth += 1;
                    }
                    ValueType::String => {
                        self.start_expected_value_type(ValueType::String)?;
                        // Write value in a streaming way using value writer
                        let mut string_writer = json_writer.string_value_writer()?;

                        let mut buf = [0_u8; 64];
                        loop {
                            let mut reached_end = false;
                            let mut read_count = 0;
                            // Buffer must have enough bytes free to read next char UTF-8 bytes
                            while buf.len() - read_count >= utf8::MAX_BYTES_PER_CHAR {
                                reached_end = self
                                    .read_string_bytes(&mut |byte| {
                                        buf[read_count] = byte;
                                        read_count += 1;
                                    })
                                    .map_err(ReaderError::from)?;

                                if reached_end {
                                    break;
                                }
                            }

                            // `read_string_bytes` call above performed validation and only placed complete UTF-8
                            // data into buffer, so unchecked conversion should be safe
                            let string = utf8::to_str_unchecked(&buf[..read_count]);
                            string_writer.write_str(string)?;
                            if reached_end {
                                break;
                            }
                        }
                        string_writer.finish_value()?;
                        self.on_value_end();
                    }
                    ValueType::Number => {
                        let number = self.next_number_as_str()?;
                        // Don't use `JsonWriter::number_value_from_string` to avoid redundant number string validation
                        // because `next_number_as_str` already made sure that number is valid
                        json_writer.number_value(TransferredNumber(number))?;
                    }
                    ValueType::Boolean => {
                        json_writer.bool_value(self.next_bool()?)?;
                    }
                    ValueType::Null => {
                        self.next_null()?;
                        json_writer.null_value()?;
                    }
                }
            }

            if depth == 0 {
                break;
            }
        }

        Ok(())
    }

    fn consume_trailing_whitespace(mut self) -> Result<(), ReaderError> {
        if self.is_string_value_reader_active {
            panic!("Incorrect reader usage: Cannot consume trailing whitespace when string value reader is active");
        }
        if self.stack.is_empty() {
            if self.is_empty {
                panic!("Incorrect reader usage: Cannot skip trailing whitespace when top-level value has not been consumed yet");
            }
        } else {
            panic!("Incorrect reader usage: Cannot skip trailing whitespace when top-level value has not been fully consumed yet");
        }

        let next_byte = self.skip_whitespace(None)?;
        return if next_byte.is_some() {
            self.create_syntax_value_error(SyntaxErrorKind::TrailingData)
        } else {
            Ok(())
        };
    }

    fn current_position(&self, include_path: bool) -> JsonReaderPosition {
        JsonReaderPosition {
            path: if include_path {
                self.json_path.clone()
            } else {
                None
            },
            line_pos: Some(LinePosition {
                line: self.line,
                column: self.column,
            }),
            data_pos: Some(self.byte_pos),
        }
    }
}

// - 1, since at least one byte was already consumed
const STRING_VALUE_READER_BUF_SIZE: usize = utf8::MAX_BYTES_PER_CHAR - 1;

struct StringValueReader<'j, R: Read> {
    json_reader: &'j mut JsonStreamReader<R>,
    /// Buffer in case multi-byte character is read but caller did not provide large enough buffer
    utf8_buf: [u8; STRING_VALUE_READER_BUF_SIZE],
    /// Start position within [utf8_buf]
    utf8_start_pos: usize,
    /// Number of bytes currently in the [utf8_buf]
    utf8_count: usize,
    reached_end: bool,
    /// The last error which occurred, and which should be returned for every subsequent `read` call
    // `io::Error` does not implement Clone, so this only contains some of its data
    error: Option<(ErrorKind, String)>,
}

impl<R: Read> StringValueReader<'_, R> {
    fn read_impl(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        if self.reached_end || buf.is_empty() {
            return Ok(0);
        }
        let mut pos = 0;
        // Check if there are remaining bytes in the UTF-8 buffer which should be served first
        if self.utf8_count > 0 {
            let copy_count = self.utf8_count.min(buf.len());
            buf[..copy_count].copy_from_slice(
                &self.utf8_buf[self.utf8_start_pos..(self.utf8_start_pos + copy_count)],
            );
            pos += copy_count;

            // Check if complete buffer content was copied
            if copy_count == self.utf8_count {
                self.utf8_start_pos = 0;
                self.utf8_count = 0;
            } else {
                self.utf8_start_pos += copy_count;
                self.utf8_count -= copy_count;
            }
        }

        while pos < buf.len() {
            // Can assume that utf8_start_pos is 0 because it should have been drained at the beginning of
            // this `read` method; otherwise if there were still remaining bytes in the UTF-8 buffer, that
            // would indicate that `buf` was too small and is already full, so no iteration of this loop
            // would have run
            debug_assert!(self.utf8_start_pos == 0 && self.utf8_count == 0);
            let result = self.json_reader.read_string_bytes(&mut |byte| {
                if pos < buf.len() {
                    buf[pos] = byte;
                    pos += 1;
                } else {
                    // Due to loop condition at least one byte was written to `buf`, so at most 3 additional bytes
                    // have to be stored in utf8_buf
                    self.utf8_buf[self.utf8_count] = byte;
                    self.utf8_count += 1;
                }
            });
            match result {
                Ok(reached_end) => {
                    if reached_end {
                        self.reached_end = true;
                        self.json_reader.is_string_value_reader_active = false;
                        self.json_reader.on_value_end();
                        break;
                    }
                }
                Err(e) => match e {
                    StringReadingError::SyntaxError(e) => {
                        return Err(IoError::new(ErrorKind::Other, e))
                    }
                    StringReadingError::IoError(e) => {
                        // Note: Could instead also directly return `Err(e.0)`; that would allow user to
                        // inspect IO error, but would on the other hand lose location information
                        return Err(IoError::new(ErrorKind::Other, e));
                    }
                },
            }
        }
        Ok(pos)
    }

    fn check_previous_error(&self) -> std::io::Result<()> {
        match &self.error {
            None => Ok(()),
            // Report as `Other` kind (and with custom message) to avoid caller indefinitely retrying
            // because it considers the original error kind as safe to retry
            Some(e) => Err(IoError::other(format!(
                "previous error '{}': {}",
                e.0,
                e.1.clone()
            ))),
        }
    }
}
impl<R: Read> Read for StringValueReader<'_, R> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.check_previous_error()?;

        let result = self.read_impl(buf);
        if let Err(e) = &result {
            self.error = Some((e.kind(), e.to_string()));
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::writer::{
        FiniteNumber, FloatingPointNumber, JsonNumberError, JsonStreamWriter, StringValueWriter,
    };

    type TestResult = Result<(), Box<dyn std::error::Error>>;

    fn new_reader(json: &str) -> JsonStreamReader<&[u8]> {
        JsonStreamReader::new(json.as_bytes())
    }

    trait IterAssert: IntoIterator
    where
        Self::Item: Display,
    {
        fn assert_all<A: FnMut(&Self::Item) -> TestResult>(self, mut assert: A)
        where
            Self: Sized,
        {
            for t in self.into_iter() {
                let result = assert(&t);
                if result.is_err() {
                    panic!("Failed for '{t}': {}", result.unwrap_err());
                }
            }
        }
    }
    impl<T: IntoIterator> IterAssert for T where T::Item: Display {}

    fn assert_parse_error_with_byte_pos<T>(
        // input is only used for display purposes; enhances error messages for loops testing multiple inputs
        input: Option<&str>,
        result: Result<T, ReaderError>,
        expected_kind: SyntaxErrorKind,
        expected_path: &JsonPath,
        expected_column: u64,
        expected_byte_pos: u64,
    ) {
        let input_display_str = input.map_or("".to_owned(), |s| format!(" for '{s}'"));
        match result {
            Ok(_) => panic!("Test should have failed{}", input_display_str),
            Err(e) => match e {
                ReaderError::SyntaxError(e) => assert_eq!(
                    JsonSyntaxError {
                        kind: expected_kind,
                        location: JsonReaderPosition {
                            path: Some(expected_path.to_vec()),
                            line_pos: Some(LinePosition {
                                line: 0,
                                column: expected_column
                            }),
                            data_pos: Some(expected_byte_pos),
                        },
                    },
                    e,
                    "For input: {:?}",
                    input
                ),
                other => {
                    panic!("Unexpected error{}: {other}", input_display_str)
                }
            },
        }
    }

    fn assert_parse_error_with_path<T>(
        // input is only used for display purposes; enhances error messages for loops testing multiple inputs
        input: Option<&str>,
        result: Result<T, ReaderError>,
        expected_kind: SyntaxErrorKind,
        expected_path: &JsonPath,
        expected_column: u64,
    ) {
        assert_parse_error_with_byte_pos(
            input,
            result,
            expected_kind,
            expected_path,
            expected_column,
            // Assume input is ASCII only on single line; treat column as byte pos
            expected_column,
        )
    }

    fn assert_parse_error<T>(
        input: Option<&str>,
        result: Result<T, ReaderError>,
        expected_kind: SyntaxErrorKind,
        expected_column: u64,
    ) {
        assert_parse_error_with_path(input, result, expected_kind, &[], expected_column);
    }

    #[test]
    fn literals() -> TestResult {
        let mut json_reader = new_reader("[true, false, null]");
        json_reader.begin_array()?;

        assert_eq!(true, json_reader.next_bool()?);
        assert_eq!(false, json_reader.next_bool()?);
        json_reader.next_null()?;

        json_reader.end_array()?;

        json_reader.consume_trailing_whitespace()?;

        Ok(())
    }

    #[test]
    fn literals_invalid() -> TestResult {
        let invalid_numbers = ["truE", "tru", "falsE", "fal", "nuLl", "nu"];
        for invalid_number in invalid_numbers {
            let mut json_reader = new_reader(invalid_number);
            assert_parse_error(
                Some(invalid_number),
                json_reader.next_number_as_string(),
                SyntaxErrorKind::InvalidLiteral,
                0,
            );
        }

        let mut json_reader = new_reader("truey");
        assert_parse_error(
            None,
            json_reader.peek(),
            SyntaxErrorKind::TrailingDataAfterLiteral,
            0,
        );

        Ok(())
    }

    /// Verifies that valid trailing data after literal does not prevent literal from being parsed
    #[test]
    fn literals_valid_trailing_data() -> TestResult {
        ["", " ", "\t", "\r", "\n", "\r\n"].assert_all(|whitespace| {
            let json = format!("true{whitespace}");
            let mut json_reader = new_reader(&json);
            assert_eq!(true, json_reader.next_bool()?);
            json_reader.consume_trailing_whitespace()?;
            Ok(())
        });

        let mut json_reader = new_reader("[true,true]");
        json_reader.begin_array()?;
        assert_eq!(true, json_reader.next_bool()?);
        assert_eq!(true, json_reader.next_bool()?);
        json_reader.end_array()?;

        let mut json_reader = new_reader(r#"{"a":true}"#);
        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name_owned()?);
        assert_eq!(true, json_reader.next_bool()?);
        json_reader.end_object()?;

        let mut json_reader = new_reader_with_comments("true// a");
        assert_eq!(true, json_reader.next_bool()?);
        json_reader.consume_trailing_whitespace()?;

        Ok(())
    }

    duplicate::duplicate! {
        [
            method;
            [next_number_as_str];
            [next_number_as_string];
        ]
        #[test]
        fn method() -> TestResult {
            let mut json_reader =
                new_reader("[0, -0, -1, -9, 123, 56.0030, -0.1, 1.01e+03, -4.50E-40]");

            json_reader.begin_array()?;

            [
                "0",
                "-0",
                "-1",
                "-9",
                "123",
                "56.0030",
                "-0.1",
                "1.01e+03",
                "-4.50E-40",
            ].assert_all(|expected| {
                assert_eq!(*expected, json_reader.method()?);
                Ok(())
            });

            json_reader.end_array()?;
            json_reader.consume_trailing_whitespace()?;


            // Also include large number to make sure value buffer is correctly reused / replaced
            let large_number = "123".repeat(READER_BUF_SIZE);
            let json = format!("[1, {large_number}, {large_number}, 2, {large_number}, 3]");
            let mut json_reader = JsonStreamReader::new_custom(
                json.as_bytes(),
                ReaderSettings {
                    restrict_number_values: false,
                    ..Default::default()
                },
            );

            json_reader.begin_array()?;

            [
                "1",
                &large_number,
                &large_number,
                "2",
                &large_number,
                "3",
            ].assert_all(|expected| {
                assert_eq!(*expected, json_reader.method()?);
                Ok(())
            });

            json_reader.end_array()?;
            json_reader.consume_trailing_whitespace()?;

            Ok(())
        }
    }

    #[test]
    fn numbers() -> TestResult {
        let mut json_reader = new_reader("[123, 45, 0.5, 0.7]");

        json_reader.begin_array()?;
        assert_eq!(123, json_reader.next_number::<i32>()??);
        // TODO This should also work without explicitly specifying `::<u32>`, but then (depending on what
        // other code in this project exists) Rust Analyzer reports errors here occasionally
        assert_eq!(45_u32, json_reader.next_number::<u32>()??);
        assert_eq!(0.5, json_reader.next_number::<f32>()??);
        // Cannot parse floating point number as i32
        assert!(json_reader.next_number::<i32>()?.is_err());

        Ok(())
    }

    #[test]
    fn numbers_invalid() -> TestResult {
        let invalid_numbers = [
            "-", "--1", "-.1", "00", "01", "1.", "1.-1", "1.e1", "1e", "1ee1", "1eE1", "1e-",
            "1e+", "1e--1", "1e+-1", "1e.1", "1e1.1", "1e1-1", "1e1e1",
        ];
        for invalid_number in invalid_numbers {
            let mut json_reader = new_reader(invalid_number);
            assert_parse_error(
                Some(invalid_number),
                json_reader.next_number_as_string(),
                SyntaxErrorKind::MalformedNumber,
                0,
            );
        }

        let mut json_reader = new_reader("+1");
        assert_parse_error(
            None,
            json_reader.next_number_as_string(),
            SyntaxErrorKind::MalformedJson,
            0,
        );

        let mut json_reader = new_reader("123a");
        assert_parse_error(
            None,
            json_reader.next_number_as_string(),
            SyntaxErrorKind::TrailingDataAfterNumber,
            3,
        );

        Ok(())
    }

    #[test]
    fn numbers_restriction() -> TestResult {
        let numbers = vec![
            "1e99".to_owned(),
            "1e+99".to_owned(),
            "1e-99".to_owned(),
            // Leading 0s should be ignored
            "1e000000".to_owned(),
            "1e0000001".to_owned(),
            "1e+0000001".to_owned(),
            "1e-0000001".to_owned(),
            "1".repeat(100),
        ];
        for number in numbers {
            let mut json_reader = new_reader(&number);
            assert_eq!(number, json_reader.next_number_as_string()?);
            json_reader.consume_trailing_whitespace()?;
        }

        fn assert_unsupported_number(number_json: &str) {
            let mut json_reader = new_reader(number_json);
            match json_reader.next_number_as_string() {
                Err(ReaderError::UnsupportedNumberValue { number, location }) => {
                    assert_eq!(number_json, number);
                    assert_eq!(
                        JsonReaderPosition {
                            path: Some(Vec::new()),
                            line_pos: Some(LinePosition { line: 0, column: 0 }),
                            data_pos: Some(0),
                        },
                        location
                    );
                }
                r => panic!("Unexpected result: {r:?}"),
            }

            let mut json_reader = new_reader(number_json);
            match json_reader.next_number::<f64>() {
                Err(ReaderError::UnsupportedNumberValue { number, location }) => {
                    assert_eq!(number_json, number);
                    assert_eq!(
                        JsonReaderPosition {
                            path: Some(Vec::new()),
                            line_pos: Some(LinePosition { line: 0, column: 0 }),
                            data_pos: Some(0),
                        },
                        location
                    );
                }
                r => panic!("Unexpected result: {r:?}"),
            }
        }

        assert_unsupported_number("1e100");
        assert_unsupported_number("1e+100");
        assert_unsupported_number("1e-100");
        assert_unsupported_number("1e000100");
        assert_unsupported_number(&"1".repeat(101));

        // Skipping should not enforce number restriction
        let mut json_reader = new_reader("1e100");
        json_reader.skip_value()?;
        json_reader.consume_trailing_whitespace()?;

        let numbers = vec![
            "1e100".to_owned(),
            "1e+100".to_owned(),
            "1e-100".to_owned(),
            "1".repeat(101),
        ];
        for number in numbers {
            let mut json_reader = JsonStreamReader::new_custom(
                number.as_bytes(),
                ReaderSettings {
                    restrict_number_values: false,
                    ..Default::default()
                },
            );
            assert_eq!(number, json_reader.next_number_as_string()?);
        }

        Ok(())
    }

    duplicate::duplicate! {
        [
            method;
            [next_str];
            [next_string];
        ]
        #[test]
        fn method() -> TestResult {
            fn pair(json_string: &str, expected_value: &str) -> (String, String) {
                (json_string.to_owned(), expected_value.to_owned())
            }

            let test_data = [
                pair("", ""),
                pair("a", "a"),
                pair("\\n", "\n"),
                pair("\\na", "\na"),
                pair("\\n\\na", "\n\na"),
                pair("a\\n", "a\n"),
                pair("a\\na\\n\\na", "a\na\n\na"),
                pair("a\u{10FFFF}", "a\u{10FFFF}"),
                ("a".repeat(READER_BUF_SIZE - 2), "a".repeat(READER_BUF_SIZE - 2)),
                ("a".repeat(READER_BUF_SIZE - 1), "a".repeat(READER_BUF_SIZE - 1)),
                ("a".repeat(READER_BUF_SIZE), "a".repeat(READER_BUF_SIZE)),
                ("a".repeat(READER_BUF_SIZE + 1), "a".repeat(READER_BUF_SIZE + 1)),
                ("a".repeat(READER_BUF_SIZE - 1) + "\\n", "a".repeat(READER_BUF_SIZE - 1) + "\n"),
                ("a".repeat(READER_BUF_SIZE) + "\\na", "a".repeat(READER_BUF_SIZE) + "\na"),
            ];
            for (json_string, expected_value) in test_data {
                let json_value = format!("\"{json_string}\"");
                let mut json_reader = new_reader(&json_value);
                assert_eq!(expected_value, json_reader.method()?);
                json_reader.consume_trailing_whitespace()?;
            }

            // Also test reading array of multiple string values, including ones which cannot
            // be read directly from reader buf array, to verify that value buffer is correctly
            // reused / replaced
            let large_json_string = "abc".repeat(READER_BUF_SIZE);
            let json_value = format!("[\"a\", \"{large_json_string}\", \"\\n\", \"{large_json_string}\", \"a\", \"\\n\"]");
            let mut json_reader = new_reader(&json_value);
            json_reader.begin_array()?;

            assert_eq!("a", json_reader.method()?);
            assert_eq!(large_json_string, json_reader.method()?);
            assert_eq!("\n", json_reader.method()?);
            assert_eq!(large_json_string, json_reader.method()?);
            assert_eq!("a", json_reader.method()?);
            assert_eq!("\n", json_reader.method()?);

            json_reader.end_array()?;
            json_reader.consume_trailing_whitespace()?;

            Ok(())
        }
    }

    #[test]
    fn strings() -> TestResult {
        let json = r#"["", "a b", "a\"b", "a\\\\\"b", "a\\", "\"\\\/\b\f\n\r\t\u0000\u0080\u0800\u12345\uD852\uDF62 \u1234\u5678\u90AB\uCDEF\uabcd\uefEF","#.to_owned() + "\"\u{007F}\u{0080}\u{07FF}\u{0800}\u{FFFF}\u{10000}\u{10FFFF}\",\"\u{2028}\u{2029}\"]";
        let mut json_reader = new_reader(&json);
        json_reader.begin_array()?;

        assert_eq!("", json_reader.next_string()?);
        assert_eq!("a b", json_reader.next_string()?);
        assert_eq!("a\"b", json_reader.next_string()?);
        assert_eq!("a\\\\\"b", json_reader.next_string()?);
        assert_eq!("a\\", json_reader.next_string()?);
        assert_eq!(
            "\"\\/\u{0008}\u{000C}\n\r\t\u{0000}\u{0080}\u{0800}\u{1234}5\u{24B62} \u{1234}\u{5678}\u{90AB}\u{CDEF}\u{ABCD}\u{EFEF}",
            json_reader.next_string()?
        );
        // Tests code points with different UTF-8 encoding length
        assert_eq!(
            "\u{007F}\u{0080}\u{07FF}\u{0800}\u{FFFF}\u{10000}\u{10FFFF}",
            json_reader.next_string()?
        );
        // Line separator (U+2028) and paragraph separator (U+2029) are not allowed by JavaScript, but are allowed unescaped by JSON
        assert_eq!("\u{2028}\u{2029}", json_reader.next_string()?);

        json_reader.end_array()?;
        json_reader.consume_trailing_whitespace()?;

        Ok(())
    }

    #[test]
    fn strings_invalid() {
        fn assert_invalid(json: &str, expected_kind: SyntaxErrorKind, expected_column: u64) {
            let mut json_reader = new_reader(json);
            assert_parse_error(
                Some(json),
                json_reader.next_string(),
                expected_kind,
                expected_column,
            );
        }

        // Missing closing double quote
        assert_invalid(r#"""#, SyntaxErrorKind::IncompleteDocument, 1);
        // Trailing backslash
        assert_invalid(r#""\"#, SyntaxErrorKind::MalformedEscapeSequence, 1);
        // Not escaped control characters
        assert_invalid(
            "\"\u{0000}\"",
            SyntaxErrorKind::NotEscapedControlCharacter,
            1,
        );
        assert_invalid(
            "\"\u{001F}\"",
            SyntaxErrorKind::NotEscapedControlCharacter,
            1,
        );
        assert_invalid("\"\n\"", SyntaxErrorKind::NotEscapedControlCharacter, 1);
        assert_invalid("\"\r\"", SyntaxErrorKind::NotEscapedControlCharacter, 1);

        // Unknown escape sequences
        assert_invalid(r#""\x12""#, SyntaxErrorKind::UnknownEscapeSequence, 1);
        assert_invalid(r#""\1234""#, SyntaxErrorKind::UnknownEscapeSequence, 1);
        assert_invalid(r#""\U1234""#, SyntaxErrorKind::UnknownEscapeSequence, 1);
        // Trying to escape LF
        assert_invalid("\"\\\n\"", SyntaxErrorKind::UnknownEscapeSequence, 1);

        // Malformed unicode escapes
        assert_invalid(r#""\u12"#, SyntaxErrorKind::MalformedEscapeSequence, 1);
        assert_invalid(r#""\u12""#, SyntaxErrorKind::MalformedEscapeSequence, 1);
        assert_invalid(r#""\uDEFG""#, SyntaxErrorKind::MalformedEscapeSequence, 1);
        assert_invalid(r#""\uu1234""#, SyntaxErrorKind::MalformedEscapeSequence, 1);
        // Switched surrogate pairs
        assert_invalid(
            r#""\uDC00\uD800""#,
            SyntaxErrorKind::UnpairedSurrogatePairEscapeSequence,
            1,
        );
        // Incomplete surrogate pair
        assert_invalid(
            r#""\uD800"#, // incomplete string value which ends with unpaired surrogate pair
            SyntaxErrorKind::UnpairedSurrogatePairEscapeSequence,
            1,
        );
        assert_invalid(
            r#""\uD800""#, // string value ends with unpaired surrogate pair
            SyntaxErrorKind::UnpairedSurrogatePairEscapeSequence,
            1,
        );

        fn assert_invalid_utf8(string_content: &[u8]) {
            let mut bytes = Vec::new();
            bytes.push(b'"');
            bytes.extend(string_content);
            bytes.push(b'"');
            let mut json_reader = JsonStreamReader::new(bytes.as_slice());
            match json_reader.next_string() {
                Err(ReaderError::IoError { error, location }) => {
                    assert_eq!(ErrorKind::InvalidData, error.kind());
                    assert_eq!("invalid UTF-8 data", error.to_string());
                    assert_eq!(Some(Vec::new()), location.path);
                    assert_eq!(0, location.line_pos.unwrap().line);
                }
                result => panic!("Unexpected result for '{string_content:?}': {result:?}"),
            }
        }

        // High surrogate followed by low surrogate in (invalid) UTF-8 encoding
        let mut json_reader = JsonStreamReader::new(b"\"\\uD800\xED\xB0\x80\"" as &[u8]);
        assert_parse_error(
            None,
            json_reader.next_string(),
            SyntaxErrorKind::UnpairedSurrogatePairEscapeSequence,
            1,
        );

        // Malformed UTF-8; high surrogate U+D800 encoded in UTF-8 (= invalid)
        assert_invalid_utf8(b"\xED\xA0\x80");

        // Malformed UTF-8; low surrogate u+DFFF encoded in UTF-8 (= invalid)
        assert_invalid_utf8(b"\xED\xBF\xBF");

        // Overlong encoding for two bytes
        assert_invalid_utf8(b"\xC1\xBF");

        // Overlong encoding for three bytes
        assert_invalid_utf8(b"\xE0\x9F\xBF");

        // Overlong encoding for four bytes
        assert_invalid_utf8(b"\xF0\x8F\xBF\xBF");

        // Greater than max code point U+10FFFF
        assert_invalid_utf8(b"\xF4\x90\x80\x80");

        // Malformed single byte
        assert_invalid_utf8(b"\x80");

        // Malformed two bytes
        assert_invalid_utf8(b"\xC2\x00");

        // Incomplete two bytes
        assert_invalid_utf8(b"\xC2");

        // Malformed three bytes
        assert_invalid_utf8(b"\xE0\xA0\x00");

        // Incomplete three bytes
        assert_invalid_utf8(b"\xE0\xA0");

        // Malformed four bytes
        assert_invalid_utf8(b"\xF0\x90\x80\x00");

        // Incomplete four bytes
        assert_invalid_utf8(b"\xF0\x90\x80");
    }

    #[test]
    fn string_reader() -> TestResult {
        let mut json_reader = new_reader("[\"test\u{10FFFF}\", true, \"ab\"]");
        json_reader.begin_array()?;

        let mut reader = json_reader.next_string_reader()?;

        let mut buf = [0; 1];
        assert_eq!(1, reader.read(&mut buf)?);
        assert_eq!(b't', buf[0]);

        assert_eq!(1, reader.read(&mut buf)?);
        assert_eq!(b'e', buf[0]);

        assert_eq!(1, reader.read(&mut buf)?);
        assert_eq!(b's', buf[0]);

        assert_eq!(1, reader.read(&mut buf)?);
        assert_eq!(b't', buf[0]);

        assert_eq!(1, reader.read(&mut buf)?);
        assert_eq!(b'\xF4', buf[0]);

        assert_eq!(1, reader.read(&mut buf)?);
        assert_eq!(b'\x8F', buf[0]);

        assert_eq!(1, reader.read(&mut buf)?);
        assert_eq!(b'\xBF', buf[0]);

        assert_eq!(1, reader.read(&mut buf)?);
        assert_eq!(b'\xBF', buf[0]);

        assert_eq!(0, reader.read(&mut buf)?);
        // Calling `read` again at end of string should have no effect
        assert_eq!(0, reader.read(&mut buf)?);
        drop(reader);

        assert_eq!(true, json_reader.next_bool()?);

        let mut reader = json_reader.next_string_reader()?;
        assert_eq!(1, reader.read(&mut buf)?);
        assert_eq!(b'a', buf[0]);

        assert_eq!(1, reader.read(&mut buf)?);
        assert_eq!(b'b', buf[0]);

        assert_eq!(0, reader.read(&mut buf)?);
        drop(reader);

        json_reader.end_array()?;
        json_reader.consume_trailing_whitespace()?;

        Ok(())
    }

    #[test]
    fn string_reader_syntax_error() -> TestResult {
        let mut json_reader = new_reader("\"\\12\"");
        let reader = json_reader.next_string_reader()?;

        match std::io::read_to_string(reader) {
            Ok(_) => panic!("Should have failed"),
            Err(e) => {
                assert_eq!(ErrorKind::Other, e.kind());
                assert_eq!(
                    "JSON syntax error UnknownEscapeSequence at path '$', line 0, column 1 (data pos 1)",
                    e.to_string()
                );
                let cause: &JsonSyntaxError = e
                    .get_ref()
                    .unwrap()
                    .downcast_ref::<JsonSyntaxError>()
                    .unwrap();
                assert_eq!(
                    &JsonSyntaxError {
                        kind: SyntaxErrorKind::UnknownEscapeSequence,
                        location: JsonReaderPosition {
                            path: Some(Vec::new()),
                            line_pos: Some(LinePosition { line: 0, column: 1 }),
                            data_pos: Some(1),
                        },
                    },
                    cause
                );
            }
        }
        Ok(())
    }

    #[test]
    fn string_reader_utf8_error() -> TestResult {
        let mut json_reader = JsonStreamReader::new(b"\"\x80\"" as &[u8]);
        let reader = json_reader.next_string_reader()?;

        match std::io::read_to_string(reader) {
            Ok(_) => panic!("Should have failed"),
            Err(e) => {
                assert_eq!(ErrorKind::Other, e.kind());
                assert_eq!(
                    "IO error 'invalid UTF-8 data' at (roughly) path '$', line 0, column 1 (data pos 1)",
                    e.get_ref().unwrap().to_string()
                );
            }
        }
        Ok(())
    }

    #[test]
    fn string_reader_repeats_error() -> TestResult {
        struct BlockingReader<'a> {
            remaining_data: &'a [u8],
        }
        /// Custom implementation which returns `WouldBlock` on end of data
        impl Read for BlockingReader<'_> {
            fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
                if buf.is_empty() {
                    return Ok(0);
                }
                if self.remaining_data.is_empty() {
                    return Err(IoError::new(ErrorKind::WouldBlock, "custom message"));
                }

                let copy_count = buf.len().min(self.remaining_data.len());
                buf[..copy_count].copy_from_slice(&self.remaining_data[..copy_count]);
                self.remaining_data = &self.remaining_data[copy_count..];
                Ok(copy_count)
            }
        }

        let mut json_reader = JsonStreamReader::new(BlockingReader {
            remaining_data: "\"test".as_bytes(),
        });
        let mut reader = json_reader.next_string_reader()?;

        let expected_original_message =
            "IO error 'custom message' at (roughly) path '$', line 0, column 5 (data pos 5)";

        let mut buf = [0_u8; 10];
        match reader.read(&mut buf) {
            Ok(_) => panic!("Should have failed"),
            Err(e) => {
                // The kind here is `Other` instead of `WouldBlock` used above because JsonStreamReader
                // wraps underlying IoError as ReaderError, and current StringValueReader implementation
                // does not unwrap it, to keep the location information
                assert_eq!(ErrorKind::Other, e.kind());
                let wrapped_error = e.get_ref().unwrap();
                assert_eq!(expected_original_message, wrapped_error.to_string());
            }
        }

        // Subsequent read attemps should fail with same error, but use custom message and kind `Other`
        match reader.read(&mut buf) {
            Ok(_) => panic!("Should have failed"),
            Err(e) => {
                assert_eq!(ErrorKind::Other, e.kind());
                // The wrapped error is actually the String message converted using `impl From<String> for Box<dyn Error>`
                let wrapped_error = e.get_ref().unwrap();
                assert_eq!(
                    format!(
                        "previous error '{}': {}",
                        ErrorKind::Other,
                        expected_original_message
                    ),
                    wrapped_error.to_string()
                );
            }
        }

        // Should still consider string value reader as active because value was not
        // successfully consumed
        drop(reader);
        assert!(json_reader.is_string_value_reader_active);

        Ok(())
    }

    #[test]
    #[should_panic(
        expected = "Incorrect reader usage: Cannot peek when string value reader is active"
    )]
    fn string_reader_incomplete() {
        let mut json_reader = new_reader("[\"ab\", true]");
        json_reader.begin_array().unwrap();

        let mut reader = json_reader.next_string_reader().unwrap();

        let mut buf = [0; 1];
        assert_eq!(1, reader.read(&mut buf).unwrap());
        drop(reader);

        json_reader.next_bool().unwrap();
    }

    /// Test string reading behavior for a reader which provides one byte at a time
    #[test]
    fn strings_single_byte_reader() -> TestResult {
        struct SingleByteReader {
            index: usize,
            bytes: &'static [u8],
        }
        impl Read for SingleByteReader {
            fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
                if buf.is_empty() || self.index >= self.bytes.len() {
                    return Ok(0);
                }
                buf[0] = self.bytes[self.index];
                self.index += 1;
                Ok(1)
            }
        }

        let reader = SingleByteReader {
            index: 0,
            bytes: "{\"name1 \u{10FFFF}\": \"value1 \u{10FFFF}\", \"name2 \u{10FFFF}\": \"value2 \u{10FFFF}\", \"name3 \u{10FFFF}\": \"value3 \u{10FFFF}\"}".as_bytes(),
        };
        let mut json_reader = JsonStreamReader::new(reader);
        json_reader.begin_object()?;

        assert_eq!("name1 \u{10FFFF}", json_reader.next_name()?);
        assert_eq!("value1 \u{10FFFF}", json_reader.next_str()?);

        assert_eq!("name2 \u{10FFFF}", json_reader.next_name_owned()?);
        assert_eq!("value2 \u{10FFFF}", json_reader.next_string()?);

        assert_eq!("name3 \u{10FFFF}", json_reader.next_name()?);
        let mut string_value_reader = json_reader.next_string_reader()?;
        let mut string = String::new();
        string_value_reader.read_to_string(&mut string)?;
        drop(string_value_reader);
        assert_eq!("value3 \u{10FFFF}", string);

        json_reader.end_object()?;
        json_reader.consume_trailing_whitespace()?;
        Ok(())
    }

    fn new_reader_with_trailing_comma(json: &str) -> JsonStreamReader<&[u8]> {
        JsonStreamReader::new_custom(
            json.as_bytes(),
            ReaderSettings {
                allow_trailing_comma: true,
                ..Default::default()
            },
        )
    }

    #[test]
    fn array_trailing_comma() -> TestResult {
        let mut json_reader = new_reader("[,]");
        json_reader.begin_array()?;
        assert_parse_error_with_path(
            None,
            json_reader.peek(),
            SyntaxErrorKind::UnexpectedComma,
            &json_path![0],
            1,
        );

        let mut json_reader = new_reader("[1,]");
        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.peek(),
            SyntaxErrorKind::TrailingCommaNotEnabled,
            &json_path![1],
            2,
        );

        let mut json_reader = new_reader("[1,\n]");
        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.peek(),
            SyntaxErrorKind::TrailingCommaNotEnabled,
            &json_path![1],
            2,
        );

        let mut json_reader = new_reader("[1,]");
        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        // Arguably `has_next()` could also return true and only next value consuming call would fail,
        // but in that case `current_position()` method contract might be violated
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::TrailingCommaNotEnabled,
            &json_path![1],
            2,
        );

        let mut json_reader = new_reader_with_trailing_comma("[1,]");
        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_eq!(false, json_reader.has_next()?);
        json_reader.end_array()?;
        json_reader.consume_trailing_whitespace()?;

        let mut json_reader = new_reader_with_trailing_comma("[,]");
        json_reader.begin_array()?;
        assert_parse_error_with_path(
            None,
            json_reader.peek(),
            SyntaxErrorKind::UnexpectedComma,
            &json_path![0],
            1,
        );

        let mut json_reader = new_reader_with_trailing_comma("[1,,]");
        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.peek(),
            SyntaxErrorKind::UnexpectedComma,
            &json_path![1],
            3,
        );

        let mut json_reader = JsonStreamReader::new_custom(
            // `,` is not allowed as separator between multiple top-level values
            "1, 2".as_bytes(),
            ReaderSettings {
                allow_trailing_comma: true,
                allow_multiple_top_level: true,
                ..Default::default()
            },
        );
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.peek(),
            SyntaxErrorKind::UnexpectedComma,
            &[],
            1,
        );

        Ok(())
    }

    #[test]
    fn array_malformed() -> TestResult {
        let mut json_reader = new_reader("[1 2]");
        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::MissingComma,
            &json_path![1],
            3,
        );

        let mut json_reader = new_reader("[1: 2]");
        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::UnexpectedColon,
            &json_path![1],
            2,
        );

        let mut json_reader = new_reader(r#"["a": 1]"#);
        json_reader.begin_array()?;
        assert_eq!("a", json_reader.next_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::UnexpectedColon,
            &json_path![1],
            4,
        );

        let mut json_reader = new_reader("[1}");
        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::UnexpectedClosingBracket,
            &json_path![1],
            2,
        );
        assert_parse_error_with_path(
            None,
            json_reader.end_array(),
            SyntaxErrorKind::UnexpectedClosingBracket,
            &json_path![1],
            2,
        );

        Ok(())
    }

    #[test]
    #[should_panic(expected = "Incorrect reader usage: Cannot end object when not inside object")]
    fn array_end_as_object() {
        let mut json_reader = new_reader("[}");
        json_reader.begin_array().unwrap();

        json_reader.end_object().unwrap();
    }

    #[test]
    fn object_trailing_comma() -> TestResult {
        let mut json_reader = new_reader("{,}");
        json_reader.begin_object()?;
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::UnexpectedComma,
            &json_path!["<?>"],
            1,
        );

        let mut json_reader = new_reader("{\"a\":1,}");
        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name_owned()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        // Arguably `has_next()` could also return true and only next name consuming call would fail,
        // but in that case `current_position()` method contract might be violated
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::TrailingCommaNotEnabled,
            &json_path!["a"],
            6,
        );

        let mut json_reader = new_reader_with_trailing_comma("{\"a\":1,}");
        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name_owned()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_eq!(false, json_reader.has_next()?);
        json_reader.end_object()?;
        json_reader.consume_trailing_whitespace()?;

        let mut json_reader = new_reader_with_trailing_comma("{,}");
        json_reader.begin_object()?;
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::UnexpectedComma,
            &json_path!["<?>"],
            1,
        );

        let mut json_reader = new_reader_with_trailing_comma("{\"a\":1,,}");
        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name_owned()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            &json_path!["a"],
            7,
        );

        Ok(())
    }

    duplicate::duplicate! {
        [
            method;
            [next_name];
            [next_name_owned];
        ]
        #[test]
        fn method() -> TestResult {
            fn pair(json_name: &str, expected_name: &str) -> (String, String) {
                (json_name.to_owned(), expected_name.to_owned())
            }

            let test_data = [
                pair("", ""),
                pair("a", "a"),
                pair("\\n", "\n"),
                pair("\\na", "\na"),
                pair("a\\n", "a\n"),
                pair("a\\na\\n\\na", "a\na\n\na"),
                pair("a\u{10FFFF}", "a\u{10FFFF}"),
                ("a".repeat(READER_BUF_SIZE - 10), "a".repeat(READER_BUF_SIZE - 10)),
                ("a".repeat(READER_BUF_SIZE) + "\\n", "a".repeat(READER_BUF_SIZE) + "\n"),
                ("a".repeat(READER_BUF_SIZE) + "\\na", "a".repeat(READER_BUF_SIZE) + "\na"),
            ];
            for (json_name, expected_name) in test_data {
                let json_value = "{\"".to_owned() + &json_name + "\": 1}";
                let mut json_reader = new_reader(&json_value);

                json_reader.begin_object()?;
                assert_eq!(expected_name, json_reader.method()?);
                assert_eq!("1", json_reader.next_number_as_string()?);
                json_reader.end_object()?;

                json_reader.consume_trailing_whitespace()?;
            }


            // Also test reading objects with multiple names, including ones which cannot
            // be read directly from reader buf array, to verify that value buffer is correctly
            // reused / replaced

            let large_name = "abc".repeat(READER_BUF_SIZE);
            let json = "{\"a\": 1, \"".to_owned() + &large_name + "\": 2, \"\\n\": 3, \"b\": 4, \"" + &large_name + "\": {\"c\": {\"\\n\": 5}}}";

            let mut json_reader = new_reader(&json);

            json_reader.begin_object()?;
            assert_eq!("a", json_reader.method()?);
            assert_eq!("1", json_reader.next_number_as_string()?);

            assert_eq!(large_name, json_reader.method()?);
            assert_eq!("2", json_reader.next_number_as_string()?);

            assert_eq!("\n", json_reader.method()?);
            assert_eq!("3", json_reader.next_number_as_string()?);

            assert_eq!("b", json_reader.method()?);
            assert_eq!("4", json_reader.next_number_as_string()?);

            assert_eq!(large_name, json_reader.method()?);
            json_reader.begin_object()?;
            assert_eq!("c", json_reader.method()?);
            json_reader.begin_object()?;
            assert_eq!("\n", json_reader.method()?);
            assert_eq!("5", json_reader.next_number_as_string()?);
            let expected_path = vec![
                JsonPathPiece::ObjectMember(large_name),
                JsonPathPiece::ObjectMember("c".to_owned()),
                JsonPathPiece::ObjectMember("\n".to_owned()),
            ];
            assert_eq!(Some(expected_path), json_reader.json_path);
            json_reader.end_object()?;
            json_reader.end_object()?;

            json_reader.end_object()?;

            json_reader.consume_trailing_whitespace()?;

            Ok(())
        }
    }

    #[test]
    fn object_member_names() -> TestResult {
        let mut json_reader = new_reader(r#"{"": 1, "a": 2, "": 3, "a": 4}"#);
        json_reader.begin_object()?;

        assert_eq!("", json_reader.next_name_owned()?);
        assert_eq!("1", json_reader.next_number_as_string()?);

        assert_eq!("a", json_reader.next_name_owned()?);
        assert_eq!("2", json_reader.next_number_as_string()?);

        assert_eq!("", json_reader.next_name_owned()?);
        assert_eq!("3", json_reader.next_number_as_string()?);

        assert_eq!("a", json_reader.next_name_owned()?);
        assert_eq!("4", json_reader.next_number_as_string()?);

        json_reader.end_object()?;
        json_reader.consume_trailing_whitespace()?;

        Ok(())
    }

    #[test]
    fn object_malformed() -> TestResult {
        let mut json_reader = new_reader("{true: 1}");
        json_reader.begin_object()?;
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            &json_path!["<?>"],
            1,
        );
        assert_parse_error_with_path(
            None,
            json_reader.next_name_owned(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            &json_path!["<?>"],
            1,
        );

        let mut json_reader = new_reader("{test: 1}");
        json_reader.begin_object()?;
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            &json_path!["<?>"],
            1,
        );
        assert_parse_error_with_path(
            None,
            json_reader.next_name_owned(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            &json_path!["<?>"],
            1,
        );

        let mut json_reader = new_reader("{: 1}");
        json_reader.begin_object()?;
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            &json_path!["<?>"],
            1,
        );
        assert_parse_error_with_path(
            None,
            json_reader.next_name_owned(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            &json_path!["<?>"],
            1,
        );

        let mut json_reader = new_reader(r#"{"a":: 1}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_eq!("a", json_reader.next_name_owned()?);
        assert_parse_error_with_path(
            None,
            json_reader.next_number_as_string(),
            SyntaxErrorKind::UnexpectedColon,
            &json_path!["a"],
            5,
        );

        let mut json_reader = new_reader(r#"{"a"}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_eq!("a", json_reader.next_name_owned()?);
        assert_parse_error_with_path(
            None,
            json_reader.peek(),
            SyntaxErrorKind::MissingColon,
            &json_path!["a"],
            4,
        );

        let mut json_reader = new_reader(r#"{"a":}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_eq!("a", json_reader.next_name_owned()?);
        assert_parse_error_with_path(
            None,
            json_reader.peek(),
            SyntaxErrorKind::UnexpectedClosingBracket,
            &json_path!["a"],
            5,
        );

        let mut json_reader = new_reader(r#"{"a" 1}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_eq!("a", json_reader.next_name_owned()?);
        assert_parse_error_with_path(
            None,
            json_reader.peek(),
            SyntaxErrorKind::MissingColon,
            &json_path!["a"],
            5,
        );

        let mut json_reader = new_reader(r#"{"a", "b": 2}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_eq!("a", json_reader.next_name_owned()?);
        assert_parse_error_with_path(
            None,
            json_reader.peek(),
            SyntaxErrorKind::MissingColon,
            &json_path!["a"],
            4,
        );

        let mut json_reader = new_reader(r#"{"a": 1 "b": 2}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_eq!("a", json_reader.next_name_owned()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::MissingComma,
            &json_path!["a"],
            8,
        );
        assert_parse_error_with_path(
            None,
            json_reader.next_name_owned(),
            SyntaxErrorKind::MissingComma,
            &json_path!["a"],
            8,
        );

        let mut json_reader = new_reader(r#"{"a": 1,, "b": 2}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_eq!("a", json_reader.next_name_owned()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            &json_path!["a"],
            8,
        );
        /* TODO: Reader currently already advances after duplicate comma, so this won't fail
         *   However it is already documented that continuing after syntax error causes unspecified behavior
        assert_parse_error_with_path(
            None,
            json_reader.next_name_owned(),
            SyntaxErrorKind::MalformedJson,
            &json_path!["a"],
            8,
        );
         */

        let mut json_reader = new_reader(r#"{"a": 1: "b": 2}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_eq!("a", json_reader.next_name_owned()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd, // Maybe a bit misleading because it also expects comma?
            &json_path!["a"],
            7,
        );
        assert_parse_error_with_path(
            None,
            json_reader.next_name_owned(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            &json_path!["a"],
            7,
        );

        let mut json_reader = new_reader("{]");
        json_reader.begin_object()?;
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            &json_path!["<?>"],
            1,
        );
        assert_parse_error_with_path(
            None,
            json_reader.next_name_owned(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            &json_path!["<?>"],
            1,
        );
        assert_parse_error_with_path(
            None,
            json_reader.end_object(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            &json_path!["<?>"],
            1,
        );

        Ok(())
    }

    #[test]
    #[should_panic(
        expected = "Incorrect reader usage: Cannot read value when expecting member name"
    )]
    fn object_name_as_bool() {
        let mut json_reader = new_reader("{true: 1}");
        json_reader.begin_object().unwrap();

        json_reader.next_bool().unwrap();
    }

    #[test]
    #[should_panic(
        expected = "Incorrect reader usage: Cannot read value when expecting member name"
    )]
    fn object_name_as_string() {
        let mut json_reader = new_reader(r#"{"a": 1}"#);
        json_reader.begin_object().unwrap();

        json_reader.next_string().unwrap();
    }

    #[test]
    #[should_panic(expected = "Incorrect reader usage: Cannot end array when not inside array")]
    fn object_end_as_array() {
        let mut json_reader = new_reader("{]");
        json_reader.begin_object().unwrap();

        json_reader.end_array().unwrap();
    }

    #[test]
    #[should_panic(
        expected = "Incorrect reader usage: Cannot end object when member value is expected"
    )]
    fn object_end_expecting_member_value() {
        let mut json_reader = new_reader(r#"{"a":1}"#);
        json_reader.begin_object().unwrap();
        assert_eq!("a", json_reader.next_name_owned().unwrap());

        json_reader.end_object().unwrap();
    }

    #[test]
    fn skip_array() -> TestResult {
        let mut json_reader = new_reader(
            r#"[true, 1, false, 2, null, 3, 123, 4, "ab", 5, [1, [2]], 6, {"a": [{"b":1}]}, 7]"#,
        );
        json_reader.begin_array()?;

        for i in 1..=7 {
            json_reader.skip_value()?;
            assert_eq!(i, json_reader.next_number::<u32>()??);
        }

        assert_unexpected_structure(
            json_reader.skip_value(),
            UnexpectedStructureKind::FewerElementsThanExpected,
            &json_path![14],
            78,
        );

        json_reader.end_array()?;
        json_reader.consume_trailing_whitespace()?;

        Ok(())
    }

    /// Test behavior when skipping deeply nested JSON arrays; should not cause stack overflow
    #[test]
    fn skip_array_deeply_nested() -> TestResult {
        let nesting_depth = 20_000;
        let json = "[".repeat(nesting_depth) + "true" + "]".repeat(nesting_depth).as_str();
        let mut json_reader = new_reader(&json);

        json_reader.skip_value()?;
        json_reader.consume_trailing_whitespace()?;

        // Also test with malformed JSON to verify that deeply nested value is actually reached
        let json = "[".repeat(nesting_depth) + "@" + "]".repeat(nesting_depth).as_str();
        let mut json_reader = new_reader(&json);
        assert_parse_error_with_path(
            None,
            json_reader.skip_value(),
            SyntaxErrorKind::MalformedJson,
            &vec![JsonPathPiece::ArrayItem(0); nesting_depth],
            nesting_depth as u64,
        );

        Ok(())
    }

    #[test]
    fn skip_object() -> TestResult {
        let mut json_reader = new_reader(r#"{"a": {"a1": [1, []]}, "b": 2, "c": 3}"#);
        json_reader.begin_object()?;

        assert_eq!("a", json_reader.next_name_owned()?);
        json_reader.skip_value()?;

        assert_eq!("b", json_reader.next_name_owned()?);
        assert_eq!("2", json_reader.next_number_as_string()?);

        json_reader.skip_name()?;
        assert_eq!("3", json_reader.next_number_as_string()?);

        json_reader.end_object()?;
        json_reader.consume_trailing_whitespace()?;

        Ok(())
    }

    /// Test behavior when skipping deeply nested JSON objects; should not cause stack overflow
    #[test]
    fn skip_object_deeply_nested() -> TestResult {
        let nesting_depth = 20_000;
        let json_start = r#"{"a":"#;
        let json = json_start.repeat(nesting_depth) + "true" + "}".repeat(nesting_depth).as_str();
        let mut json_reader = new_reader(&json);

        json_reader.skip_value()?;
        json_reader.consume_trailing_whitespace()?;

        // Also test with malformed JSON to verify that deeply nested value is actually reached
        let json = json_start.repeat(nesting_depth) + "@" + "}".repeat(nesting_depth).as_str();
        let mut json_reader = new_reader(&json);
        assert_parse_error_with_path(
            None,
            json_reader.skip_value(),
            SyntaxErrorKind::MalformedJson,
            &vec![JsonPathPiece::ObjectMember("a".to_owned()); nesting_depth],
            (json_start.len() * nesting_depth) as u64,
        );

        Ok(())
    }

    #[test]
    fn skip_top_level() -> TestResult {
        [
            "true",
            "false",
            "null",
            "12",
            "\"ab\"",
            r#"[true, [{"a":[2]}]]"#,
            r#"{"a":[[{"a1":2}]], "b":2}"#,
        ]
        .assert_all(|json_value| {
            let mut json_reader = new_reader(json_value);
            json_reader.skip_value()?;
            json_reader.consume_trailing_whitespace()?;

            Ok(())
        });

        let mut json_reader = new_reader(r#"[]"#);
        json_reader.begin_array()?;
        assert_unexpected_structure(
            json_reader.skip_value(),
            UnexpectedStructureKind::FewerElementsThanExpected,
            &json_path![0],
            1,
        );

        let mut json_reader = new_reader(r#""#);
        assert_parse_error(
            None,
            json_reader.skip_value(),
            SyntaxErrorKind::IncompleteDocument,
            0,
        );

        Ok(())
    }

    #[test]
    #[should_panic(
        expected = "Incorrect reader usage: Cannot skip value when expecting member name"
    )]
    fn skip_value_expecting_name() {
        let mut json_reader = new_reader(r#"{"a": 1}"#);
        json_reader.begin_object().unwrap();

        json_reader.skip_value().unwrap();
    }

    #[test]
    #[should_panic(
        expected = "Incorrect reader usage: Cannot consume member name when not expecting it"
    )]
    fn skip_name_expecting_value() {
        let mut json_reader = new_reader("\"a\"");

        json_reader.skip_name().unwrap();
    }

    #[test]
    fn seek_to() -> TestResult {
        let mut json_reader = new_reader(r#"[1, {"a": 2, "b": {"c": [3, 4]}, "b": 5}]"#);
        json_reader.seek_to(&json_path![1, "b", "c", 0])?;
        assert_eq!("3", json_reader.next_number_as_string()?);

        assert_eq!(ValueType::Number, json_reader.peek()?);
        // Calling seek_to with empty path should have no effect
        json_reader.seek_to(&[])?;
        assert_eq!("4", json_reader.next_number_as_string()?);

        Ok(())
    }

    #[test]
    fn skip_to_top_level() -> TestResult {
        let mut json_reader = new_reader("null");
        // Should have no effect when not inside array or object
        json_reader.skip_to_top_level()?;
        json_reader.next_null()?;
        // Should have no effect when not inside array or object
        json_reader.skip_to_top_level()?;
        json_reader.skip_to_top_level()?;
        json_reader.consume_trailing_whitespace()?;

        let mut json_reader = new_reader(r#"[1, {"a": 2, "b": {"c": [3, 4]}, "b": 5}]"#);
        json_reader.seek_to(&json_path![1, "b", "c", 0])?;
        assert_eq!("3", json_reader.next_number_as_string()?);
        json_reader.skip_to_top_level()?;
        json_reader.consume_trailing_whitespace()?;

        let mut json_reader = new_reader(r#"{"a": 1}"#);
        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name_owned()?);
        // Should also work when currently expecting member value
        json_reader.skip_to_top_level()?;
        json_reader.consume_trailing_whitespace()?;

        let mut json_reader = new_reader(r#"[@]"#);
        json_reader.begin_array()?;
        // Should be able to detect syntax errors
        assert_parse_error_with_path(
            None,
            json_reader.skip_to_top_level(),
            SyntaxErrorKind::MalformedJson,
            &json_path![0],
            1,
        );

        Ok(())
    }

    #[test]
    fn skip_to_top_level_multi_top_level() -> TestResult {
        let mut json_reader = JsonStreamReader::new_custom(
            "[1] [2] [3]".as_bytes(),
            ReaderSettings {
                allow_multiple_top_level: true,
                ..Default::default()
            },
        );
        json_reader.begin_array()?;
        json_reader.skip_to_top_level()?;
        json_reader.begin_array()?;
        assert_eq!("2", json_reader.next_number_as_string()?);
        json_reader.skip_to_top_level()?;

        // Should have no effect since there is currently no enclosing array
        json_reader.skip_to_top_level()?;
        json_reader.skip_to_top_level()?;

        json_reader.begin_array()?;
        assert_eq!("3", json_reader.next_number_as_string()?);
        json_reader.skip_to_top_level()?;
        json_reader.consume_trailing_whitespace()?;

        Ok(())
    }

    fn as_transfer_read_error(error: TransferError) -> ReaderError {
        match error {
            TransferError::ReaderError(e) => e,
            _ => panic!("Unexpected error: {error}"),
        }
    }

    #[test]
    fn transfer_to() -> TestResult {
        let json =
            r#"[true, null, 123, 123.0e+0, "a\"b\\c\u0064", [1], {"a": 1, "a\"b\\c\u0064": 2, "c":[{"d":[3]}]},"#
                .to_owned()
                + "\"\u{10FFFF}\"]";
        let mut json_reader = new_reader(&json);
        json_reader.begin_array()?;

        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_array()?;

        while json_reader.has_next()? {
            json_reader.transfer_to(&mut json_writer)?;
        }
        // Also check how missing value is handled
        assert_unexpected_structure_with_byte_pos(
            json_reader
                .transfer_to(&mut json_writer)
                .map_err(as_transfer_read_error),
            UnexpectedStructureKind::FewerElementsThanExpected,
            &json_path![8],
            99,
            102,
        );

        json_reader.end_array()?;
        json_reader.consume_trailing_whitespace()?;

        json_writer.end_array()?;
        json_writer.finish_document()?;
        assert_eq!(
            r#"[true,null,123,123.0e+0,"a\"b\\cd",[1],{"a":1,"a\"b\\cd":2,"c":[{"d":[3]}]},"#
                .to_owned()
                + "\"\u{10FFFF}\"]",
            String::from_utf8(writer)?
        );

        Ok(())
    }

    #[test]
    fn transfer_to_large_string() -> TestResult {
        let repeat_count = 1000;
        let json = format!(
            "\"{}\"",
            // includes redundant escape `\u0062` for 'b'; this verifies that regular string writing
            // of JsonWriter is used and bytes are not just copied
            "a\\u0062 \\n \\u0000 \u{007F}\u{0080}\u{07FF}\u{0800}\u{FFFF}\u{10000}\u{10FFFF}"
                .repeat(repeat_count)
        );
        let expected_json = format!(
            "\"{}\"",
            "ab \\n \\u0000 \u{007F}\u{0080}\u{07FF}\u{0800}\u{FFFF}\u{10000}\u{10FFFF}"
                .repeat(repeat_count)
        );
        let mut json_reader = new_reader(&json);

        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_reader.transfer_to(&mut json_writer)?;
        json_reader.consume_trailing_whitespace()?;
        json_writer.finish_document()?;

        assert_eq!(expected_json, String::from_utf8(writer)?);
        Ok(())
    }

    #[test]
    fn transfer_to_string_syntax_error() {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);

        let mut json_reader = new_reader(r#""\X""#);
        // Make sure that syntax error is reported as JsonSyntaxError and not wrapped in std::io::Error
        assert_parse_error(
            None,
            json_reader
                .transfer_to(&mut json_writer)
                .map_err(as_transfer_read_error),
            SyntaxErrorKind::UnknownEscapeSequence,
            1,
        );
    }

    #[test]
    #[should_panic(
        expected = "Incorrect reader usage: Cannot transfer value when expecting member name"
    )]
    fn transfer_to_name() {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        let mut json_reader = new_reader(r#"{"a": 1}"#);
        json_reader.begin_object().unwrap();

        json_reader.transfer_to(&mut json_writer).unwrap();
    }

    #[test]
    fn transfer_to_comments() -> TestResult {
        let mut json_reader = new_reader_with_comments("[\n// test\n1,/* */2]");

        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);

        json_reader.transfer_to(&mut json_writer)?;
        json_reader.consume_trailing_whitespace()?;

        json_writer.finish_document()?;
        // Whitespace and comments are not preserved
        assert_eq!("[1,2]", String::from_utf8(writer)?);

        Ok(())
    }

    #[test]
    fn transfer_to_writer_error() {
        struct FailingJsonWriter;

        fn err() -> IoError {
            IoError::new(ErrorKind::Other, "test error")
        }

        // JsonWriter which always returns Err(...)
        // Note: If maintaining this becomes too cumbersome when adjusting JsonWriter API, can remove this test
        impl JsonWriter for FailingJsonWriter {
            fn begin_object(&mut self) -> Result<(), IoError> {
                Err(err())
            }

            fn end_object(&mut self) -> Result<(), IoError> {
                Err(err())
            }

            fn begin_array(&mut self) -> Result<(), IoError> {
                Err(err())
            }

            fn end_array(&mut self) -> Result<(), IoError> {
                Err(err())
            }

            fn name(&mut self, _: &str) -> Result<(), IoError> {
                Err(err())
            }

            fn null_value(&mut self) -> Result<(), IoError> {
                Err(err())
            }

            fn bool_value(&mut self, _: bool) -> Result<(), IoError> {
                Err(err())
            }

            fn string_value(&mut self, _: &str) -> Result<(), IoError> {
                Err(err())
            }

            fn string_value_writer(&mut self) -> Result<Box<dyn StringValueWriter + '_>, IoError> {
                Err(err())
            }

            fn number_value_from_string(&mut self, _: &str) -> Result<(), JsonNumberError> {
                Err(JsonNumberError::IoError(err()))
            }

            fn number_value<N: FiniteNumber>(&mut self, _: N) -> Result<(), IoError> {
                Err(err())
            }

            fn fp_number_value<N: FloatingPointNumber>(
                &mut self,
                _: N,
            ) -> Result<(), JsonNumberError> {
                Err(JsonNumberError::IoError(err()))
            }

            #[cfg(feature = "serde")]
            fn serialize_value<S: ::serde::ser::Serialize>(
                &mut self,
                _value: &S,
            ) -> Result<(), crate::serde::SerializerError> {
                panic!("Not needed for test")
            }

            fn finish_document(self) -> Result<(), IoError> {
                Err(err())
            }
        }

        let json_values = ["true", "null", "123", "\"a\"", "[]", "{}"];
        for json in json_values {
            let mut json_reader = new_reader(json);

            let result = json_reader.transfer_to(&mut FailingJsonWriter);
            match result {
                Ok(_) => panic!("Should have failed"),
                Err(e) => match e {
                    TransferError::ReaderError(e) => {
                        panic!("Unexpected error for input '{json}': {e:?}")
                    }
                    TransferError::WriterError(e) => {
                        assert_eq!(ErrorKind::Other, e.kind());
                        assert_eq!("test error", e.to_string());
                    }
                },
            }
        }
    }

    #[test]
    fn excessive_whitespace() -> TestResult {
        let json = r#"


            {
                "a"
                :
                [
                    
                    true,

                    false

                    ,      {          }

                ],

                "b"   :     true
                ,         "c"
                :   false
            }


        "#;

        // Test `transfer_to`
        let mut json_reader = new_reader(json);
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_reader.transfer_to(&mut json_writer)?;
        json_reader.consume_trailing_whitespace()?;
        json_writer.finish_document()?;
        assert_eq!(
            "{\"a\":[true,false,{}],\"b\":true,\"c\":false}",
            String::from_utf8(writer)?
        );

        // Test `skip_value`
        let mut json_reader = new_reader(json);
        json_reader.skip_value()?;
        json_reader.consume_trailing_whitespace()?;

        Ok(())
    }

    #[test]
    fn trailing_data() -> TestResult {
        let mut json_reader = new_reader("1 2");
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error(
            None,
            json_reader.consume_trailing_whitespace(),
            SyntaxErrorKind::TrailingData,
            2,
        );
        Ok(())
    }

    #[test]
    #[should_panic(
        expected = "Incorrect reader usage: Cannot skip trailing whitespace when top-level value has not been consumed yet"
    )]
    fn consume_trailing_whitespace_top_level_not_started() {
        let json_reader = new_reader("");

        json_reader.consume_trailing_whitespace().unwrap();
    }

    #[test]
    #[should_panic(
        expected = "Incorrect reader usage: Cannot skip trailing whitespace when top-level value has not been fully consumed yet"
    )]
    fn consume_trailing_whitespace_top_level_not_finished() {
        let mut json_reader = new_reader("[]");
        json_reader.begin_array().unwrap();

        json_reader.consume_trailing_whitespace().unwrap();
    }

    /// Byte order mark U+FEFF should not be allowed
    #[test]
    fn byte_order_mark() {
        let mut json_reader = new_reader("\u{FEFF}1");
        assert_parse_error(
            None,
            json_reader.next_number_as_string(),
            SyntaxErrorKind::MalformedJson,
            0,
        );
    }

    fn assert_unexpected_value_type<T>(
        result: Result<T, ReaderError>,
        expected_expected: ValueType,
        expected_actual: ValueType,
        expected_path: &JsonPath,
        expected_column: u64,
    ) {
        match result {
            Ok(_) => panic!("Test should have failed"),
            Err(e) => match e {
                ReaderError::UnexpectedValueType {
                    expected,
                    actual,
                    location,
                } => {
                    assert_eq!(expected_expected, expected);
                    assert_eq!(expected_actual, actual);
                    assert_eq!(
                        JsonReaderPosition {
                            path: Some(expected_path.to_vec()),
                            line_pos: Some(LinePosition {
                                line: 0,
                                column: expected_column
                            }),
                            // Assume input is ASCII only on single line; treat column as byte pos
                            data_pos: Some(expected_column),
                        },
                        location
                    );
                }
                other => {
                    panic!("Unexpected error: {other}")
                }
            },
        }
    }

    fn assert_unexpected_structure_with_byte_pos<T>(
        result: Result<T, ReaderError>,
        expected_kind: UnexpectedStructureKind,
        expected_path: &JsonPath,
        expected_column: u64,
        expected_byte_pos: u64,
    ) {
        match result {
            Ok(_) => panic!("Test should have failed"),
            Err(e) => match e {
                ReaderError::UnexpectedStructure { kind, location } => {
                    assert_eq!(expected_kind, kind);
                    assert_eq!(
                        JsonReaderPosition {
                            path: Some(expected_path.to_vec()),
                            line_pos: Some(LinePosition {
                                line: 0,
                                column: expected_column
                            }),
                            data_pos: Some(expected_byte_pos),
                        },
                        location
                    );
                }
                other => {
                    panic!("Unexpected error: {other}")
                }
            },
        }
    }

    fn assert_unexpected_structure<T>(
        result: Result<T, ReaderError>,
        expected_kind: UnexpectedStructureKind,
        expected_path: &JsonPath,
        expected_column: u64,
    ) {
        assert_unexpected_structure_with_byte_pos(
            result,
            expected_kind,
            expected_path,
            expected_column,
            // Assume input is ASCII only on single line; treat column as byte pos
            expected_column,
        )
    }

    #[test]
    fn seek_to_unexpected_structure() -> TestResult {
        let mut json_reader = new_reader("[]");
        assert_unexpected_structure(
            json_reader.seek_to(&[JsonPathPiece::ArrayItem(0)]),
            UnexpectedStructureKind::TooShortArray { expected_index: 0 },
            &json_path![0],
            1,
        );

        let mut json_reader = new_reader("[1]");
        assert_unexpected_structure(
            json_reader.seek_to(&[JsonPathPiece::ArrayItem(1)]),
            UnexpectedStructureKind::TooShortArray { expected_index: 1 },
            &json_path![1],
            2,
        );

        let mut json_reader = new_reader(r#"{"a": 1}"#);
        assert_unexpected_structure(
            json_reader.seek_to(&[JsonPathPiece::ObjectMember("b".to_owned())]),
            UnexpectedStructureKind::MissingObjectMember {
                member_name: "b".to_owned(),
            },
            &json_path!["a"],
            7,
        );

        let mut json_reader = new_reader("1");
        assert_unexpected_value_type(
            json_reader.seek_to(&[JsonPathPiece::ArrayItem(0)]),
            ValueType::Array,
            ValueType::Number,
            &[],
            0,
        );

        let mut json_reader = new_reader("1");
        assert_unexpected_value_type(
            json_reader.seek_to(&[JsonPathPiece::ObjectMember("a".to_owned())]),
            ValueType::Object,
            ValueType::Number,
            &[],
            0,
        );

        Ok(())
    }

    #[test]
    fn unexpected_structure() -> TestResult {
        let mut json_reader = new_reader("[]");
        json_reader.begin_array()?;
        assert_unexpected_structure(
            json_reader.peek(),
            UnexpectedStructureKind::FewerElementsThanExpected,
            &json_path![0],
            1,
        );
        assert_unexpected_structure(
            json_reader.next_bool(),
            UnexpectedStructureKind::FewerElementsThanExpected,
            &json_path![0],
            1,
        );

        let mut json_reader = new_reader("[1]");
        json_reader.begin_array()?;
        assert_unexpected_structure(
            json_reader.end_array(),
            UnexpectedStructureKind::MoreElementsThanExpected,
            &json_path![0],
            1,
        );

        let mut json_reader = new_reader("{}");
        json_reader.begin_object()?;
        assert_unexpected_structure(
            json_reader.next_name_owned(),
            UnexpectedStructureKind::FewerElementsThanExpected,
            &json_path!["<?>"],
            1,
        );

        let mut json_reader = new_reader(r#"{"a": 1}"#);
        json_reader.begin_object()?;
        assert_unexpected_structure(
            json_reader.end_object(),
            UnexpectedStructureKind::MoreElementsThanExpected,
            &json_path!["<?>"],
            1,
        );

        Ok(())
    }

    #[test]
    fn unexpected_value_type() {
        let mut json_reader = new_reader("1");
        assert_unexpected_value_type(
            json_reader.next_bool(),
            ValueType::Boolean,
            ValueType::Number,
            &[],
            0,
        );
        assert_unexpected_value_type(
            json_reader.next_null(),
            ValueType::Null,
            ValueType::Number,
            &[],
            0,
        );
        assert_unexpected_value_type(
            json_reader.next_string(),
            ValueType::String,
            ValueType::Number,
            &[],
            0,
        );
        assert_unexpected_value_type(
            json_reader.begin_array(),
            ValueType::Array,
            ValueType::Number,
            &[],
            0,
        );
        assert_unexpected_value_type(
            json_reader.begin_object(),
            ValueType::Object,
            ValueType::Number,
            &[],
            0,
        );

        let mut json_reader = new_reader("true");
        assert_unexpected_value_type(
            json_reader.next_number_as_string(),
            ValueType::Number,
            ValueType::Boolean,
            &[],
            0,
        );

        let mut json_reader = new_reader("false");
        assert_unexpected_value_type(
            json_reader.next_null(),
            ValueType::Null,
            ValueType::Boolean,
            &[],
            0,
        );

        let mut json_reader = new_reader("null");
        assert_unexpected_value_type(
            json_reader.next_bool(),
            ValueType::Boolean,
            ValueType::Null,
            &[],
            0,
        );

        let mut json_reader = new_reader("\"ab\"");
        assert_unexpected_value_type(
            json_reader.next_bool(),
            ValueType::Boolean,
            ValueType::String,
            &[],
            0,
        );

        let mut json_reader = new_reader("[]");
        assert_unexpected_value_type(
            json_reader.next_bool(),
            ValueType::Boolean,
            ValueType::Array,
            &[],
            0,
        );

        let mut json_reader = new_reader("{}");
        assert_unexpected_value_type(
            json_reader.next_bool(),
            ValueType::Boolean,
            ValueType::Object,
            &[],
            0,
        );
    }

    #[test]
    fn multiple_top_level() -> TestResult {
        let mut json_reader = JsonStreamReader::new_custom(
            "[1] [2]".as_bytes(),
            ReaderSettings {
                allow_multiple_top_level: true,
                ..Default::default()
            },
        );

        assert_eq!(ValueType::Array, json_reader.peek()?);
        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        json_reader.end_array()?;

        assert!(json_reader.has_next()?);
        assert_eq!(ValueType::Array, json_reader.peek()?);
        json_reader.begin_array()?;
        assert_eq!("2", json_reader.next_number_as_string()?);
        json_reader.end_array()?;

        assert_eq!(false, json_reader.has_next()?);
        assert_unexpected_structure(
            json_reader.peek(),
            UnexpectedStructureKind::FewerElementsThanExpected,
            &[],
            7,
        );
        assert_unexpected_structure(
            json_reader.next_bool(),
            UnexpectedStructureKind::FewerElementsThanExpected,
            &[],
            7,
        );

        json_reader.consume_trailing_whitespace()?;

        Ok(())
    }

    #[test]
    #[should_panic(
        expected = "Incorrect reader usage: Cannot peek when top-level value has already been consumed and multiple top-level values are not enabled in settings"
    )]
    fn multiple_top_level_disallowed() {
        let mut json_reader = new_reader("1 2");
        assert_eq!("1", json_reader.next_number_as_string().unwrap());

        json_reader.next_number_as_string().unwrap();
    }

    #[test]
    #[should_panic(
        expected = "Incorrect reader usage: Cannot check for next element when top-level value has not been started"
    )]
    fn has_next_start_of_document() {
        let mut json_reader = JsonStreamReader::new_custom(
            "[1]".as_bytes(),
            ReaderSettings {
                allow_multiple_top_level: true,
                ..Default::default()
            },
        );

        json_reader.has_next().unwrap();
    }

    #[test]
    #[should_panic(
        expected = "Incorrect reader usage: Cannot check for next element when member value is expected"
    )]
    fn has_next_member_value() {
        let mut json_reader = new_reader(r#"{"a": 1}"#);
        json_reader.begin_object().unwrap();
        assert_eq!("a", json_reader.next_name_owned().unwrap());

        json_reader.has_next().unwrap();
    }

    #[test]
    fn malformed_whitespace() {
        // Cannot use escape sequences outside of string values
        let mut json_reader = new_reader("\\u0020");
        assert_parse_error(None, json_reader.peek(), SyntaxErrorKind::MalformedJson, 0);

        let mut json_reader = new_reader("\\n");
        assert_parse_error(None, json_reader.peek(), SyntaxErrorKind::MalformedJson, 0);

        let mut json_reader = new_reader("\\r");
        assert_parse_error(None, json_reader.peek(), SyntaxErrorKind::MalformedJson, 0);

        let mut json_reader = new_reader("\\t");
        assert_parse_error(None, json_reader.peek(), SyntaxErrorKind::MalformedJson, 0);

        // Form feed (U+000C) is not allowed as whitespace
        let mut json_reader = new_reader("\u{000C}");
        assert_parse_error(None, json_reader.peek(), SyntaxErrorKind::MalformedJson, 0);

        // Line separator (U+2028), recognized by JavaScript but not allowed as whitespace for JSON
        let mut json_reader = new_reader("\u{2028}");
        assert_parse_error(None, json_reader.peek(), SyntaxErrorKind::MalformedJson, 0);

        // Paragraph separator (U+2029), recognized by JavaScript but not allowed as whitespace for JSON
        let mut json_reader = new_reader("\u{2029}");
        assert_parse_error(None, json_reader.peek(), SyntaxErrorKind::MalformedJson, 0);
    }

    fn new_reader_with_comments(json: &str) -> JsonStreamReader<&[u8]> {
        JsonStreamReader::new_custom(
            json.as_bytes(),
            ReaderSettings {
                allow_comments: true,
                ..Default::default()
            },
        )
    }

    #[test]
    fn comments() -> TestResult {
        let mut json_reader = new_reader("/");
        assert_parse_error(
            None,
            json_reader.peek(),
            SyntaxErrorKind::CommentsNotEnabled,
            0,
        );

        [
            "/* a */1",
            " /* a */ 1",
            "/**/1",
            "/***/1",
            "/* // */1",
            "/* \n \r \r\n */1",
            "/* \u{0000} */1", // unescaped control characters are allowed in comments
            "1/* 1 */",
            "//\n1",
            "// a\n1",
            "// /* a\n1",
            "// a\n// b\r// c\r\n1",
            "1// a",
            "1// a\n",
            "1//",
        ]
        .assert_all(|json_input| {
            let mut json_reader = new_reader_with_comments(json_input);
            assert_eq!("1", json_reader.next_number_as_string()?);
            json_reader.consume_trailing_whitespace()?;

            Ok(())
        });

        let mut json_reader = new_reader_with_comments(
            r#"/* a */ /* a * b * / */ [/* // a, ] */1/**/,/**/ /***/2, {/**/"a"/**/:/**/1/**/,"b"/**/:/**/2/**/}/**/]/**/"#,
        );
        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_eq!("2", json_reader.next_number_as_string()?);

        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name_owned()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_eq!("b", json_reader.next_name_owned()?);
        assert_eq!("2", json_reader.next_number_as_string()?);
        json_reader.end_object()?;

        json_reader.end_array()?;
        json_reader.consume_trailing_whitespace()?;

        let mut json_reader =
            new_reader_with_comments("[// */ a]\n1//, 4 // 5\r// first\r\n//second\n, 2]// test");
        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_eq!("2", json_reader.next_number_as_string()?);
        json_reader.end_array()?;
        json_reader.consume_trailing_whitespace()?;

        let mut json_reader = new_reader_with_comments("/* a */");
        assert_parse_error(
            None,
            json_reader.peek(),
            SyntaxErrorKind::IncompleteDocument,
            7,
        );

        let mut json_reader = new_reader_with_comments("// a");
        assert_parse_error(
            None,
            json_reader.peek(),
            SyntaxErrorKind::IncompleteDocument,
            4,
        );

        Ok(())
    }

    #[test]
    fn comments_malformed() -> TestResult {
        let mut json_reader = new_reader_with_comments("/ a");
        assert_parse_error(
            None,
            json_reader.peek(),
            SyntaxErrorKind::IncompleteComment,
            1,
        );

        let mut json_reader = new_reader_with_comments("/");
        assert_parse_error(
            None,
            json_reader.peek(),
            SyntaxErrorKind::IncompleteComment,
            1,
        );

        let mut json_reader = new_reader_with_comments("1/");
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error(
            None,
            json_reader.consume_trailing_whitespace(),
            SyntaxErrorKind::IncompleteComment,
            2,
        );

        let mut json_reader = new_reader_with_comments("/*");
        assert_parse_error(
            None,
            json_reader.peek(),
            SyntaxErrorKind::BlockCommentNotClosed,
            2,
        );

        let mut json_reader = new_reader_with_comments("/* a");
        assert_parse_error(
            None,
            json_reader.peek(),
            SyntaxErrorKind::BlockCommentNotClosed,
            4,
        );

        let mut json_reader = new_reader_with_comments("/* a /");
        assert_parse_error(
            None,
            json_reader.peek(),
            SyntaxErrorKind::BlockCommentNotClosed,
            6,
        );

        let mut json_reader = new_reader_with_comments("/* a //");
        assert_parse_error(
            None,
            json_reader.peek(),
            SyntaxErrorKind::BlockCommentNotClosed,
            7,
        );

        let mut json_reader = new_reader_with_comments("/*/");
        assert_parse_error(
            None,
            json_reader.peek(),
            SyntaxErrorKind::BlockCommentNotClosed,
            3,
        );

        let mut json_reader = new_reader_with_comments("1/*");
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error(
            None,
            json_reader.consume_trailing_whitespace(),
            SyntaxErrorKind::BlockCommentNotClosed,
            3,
        );

        let mut json_reader = new_reader_with_comments("*/");
        assert_parse_error(None, json_reader.peek(), SyntaxErrorKind::MalformedJson, 0);

        // Malformed single byte
        let mut json_reader = JsonStreamReader::new_custom(
            b"/*\x80*/" as &[u8],
            ReaderSettings {
                allow_comments: true,
                ..Default::default()
            },
        );
        match &json_reader.peek() {
            e @ Err(ReaderError::IoError { error, location }) => {
                assert_eq!(ErrorKind::InvalidData, error.kind());
                assert_eq!("invalid UTF-8 data", error.to_string());
                assert_eq!(
                    &JsonReaderPosition {
                        path: Some(Vec::new()),
                        line_pos: Some(LinePosition { line: 0, column: 2 }),
                        data_pos: Some(2),
                    },
                    location
                );
                assert_eq!(
                    "IO error 'invalid UTF-8 data' at (roughly) path '$', line 0, column 2 (data pos 2)",
                    e.as_ref().unwrap_err().to_string()
                );
            }
            result => panic!("Unexpected result: {result:?}"),
        }

        Ok(())
    }

    #[test]
    fn current_position() -> TestResult {
        let mut json_reader = JsonStreamReader::new_custom(
            r#"  [  1  , {  "a"  : true  }  ]  "#.as_bytes(),
            ReaderSettings {
                allow_multiple_top_level: true,
                ..Default::default()
            },
        );

        // Test `include_path=true`
        let position = json_reader.current_position(true);
        assert_eq!(
            JsonReaderPosition {
                path: Some(Vec::new()),
                line_pos: Some(LinePosition { line: 0, column: 0 }),
                data_pos: Some(0)
            },
            position
        );

        // Test `include_path=false`
        let position = json_reader.current_position(false);
        assert_eq!(
            JsonReaderPosition {
                path: None,
                line_pos: Some(LinePosition { line: 0, column: 0 }),
                data_pos: Some(0)
            },
            position
        );

        fn assert_pos(
            json_reader: &JsonStreamReader<impl Read>,
            expected_path: &JsonPath,
            expected_column: u64,
        ) {
            let position = json_reader.current_position(true);
            assert_eq!(
                JsonReaderPosition {
                    path: Some(expected_path.to_vec()),
                    line_pos: Some(LinePosition {
                        line: 0,
                        column: expected_column,
                    }),
                    // Assume input is ASCII only on single line; treat column as byte pos
                    data_pos: Some(expected_column)
                },
                position
            );
        }

        // Note: The expected column position before `has_next()` and `peek()` calls below just
        // represents the value returned by the current implementation; the `current_position()`
        // doc says the value is unspecified unless `has_next()` or `peek()` has been called
        assert_pos(&json_reader, &json_path![], 0);
        assert_eq!(ValueType::Array, json_reader.peek()?);
        assert_pos(&json_reader, &json_path![], 2);
        json_reader.begin_array()?;
        assert_pos(&json_reader, &json_path![0], 3);
        assert!(json_reader.has_next()?);
        assert_pos(&json_reader, &json_path![0], 5);
        assert_eq!("1", json_reader.next_number_as_str()?);
        assert_pos(&json_reader, &json_path![1], 6);
        assert!(json_reader.has_next()?);
        assert_pos(&json_reader, &json_path![1], 10);
        json_reader.begin_object()?;
        assert_pos(&json_reader, &json_path![1, "<?>"], 11);
        assert!(json_reader.has_next()?);
        assert_pos(&json_reader, &json_path![1, "<?>"], 13);
        assert_eq!("a", json_reader.next_name()?);
        assert_pos(&json_reader, &json_path![1, "a"], 16);
        assert_eq!(ValueType::Boolean, json_reader.peek()?);
        assert_pos(&json_reader, &json_path![1, "a"], 20);
        assert_eq!(true, json_reader.next_bool()?);
        assert_pos(&json_reader, &json_path![1, "a"], 24);
        assert!(!json_reader.has_next()?);
        assert_pos(&json_reader, &json_path![1, "a"], 26);
        json_reader.end_object()?;
        assert_pos(&json_reader, &json_path![2], 27);
        assert!(!json_reader.has_next()?);
        assert_pos(&json_reader, &json_path![2], 29);
        json_reader.end_array()?;
        assert_pos(&json_reader, &json_path![], 30);
        // Check for another top-level value
        assert!(!json_reader.has_next()?);
        assert_pos(&json_reader, &json_path![], 32);

        Ok(())
    }

    #[test]
    fn location_whitespace() {
        fn assert_location(
            json: &str,
            expected_line: u64,
            expected_column: u64,
            expected_byte_pos: u64,
        ) {
            let mut json_reader = new_reader_with_comments(json);
            match json_reader.peek() {
                Ok(_) => panic!("Test should have failed"),
                Err(e) => match e {
                    ReaderError::SyntaxError(e) => assert_eq!(
                        JsonSyntaxError {
                            kind: SyntaxErrorKind::IncompleteDocument,
                            location: JsonReaderPosition {
                                path: Some(Vec::new()),
                                line_pos: Some(LinePosition {
                                    line: expected_line,
                                    column: expected_column
                                }),
                                data_pos: Some(expected_byte_pos),
                            },
                        },
                        e
                    ),
                    other => {
                        panic!("Unexpected error: {other}")
                    }
                },
            }
        }

        assert_location("", 0, 0, 0);
        assert_location(" ", 0, 1, 1);
        assert_location("\t", 0, 1, 1);
        assert_location("\n", 1, 0, 1);
        assert_location("\r", 1, 0, 1);
        assert_location("\r\n", 1, 0, 2);
        assert_location("\r \n", 2, 0, 3);
        assert_location("\n\r", 2, 0, 2);
        assert_location("\r\n\n", 2, 0, 3);
        assert_location("\r\r", 2, 0, 2);
        assert_location("\r\r\n", 2, 0, 3);
        assert_location("\n  \r \t \r\n    \t\t ", 3, 7, 16);

        assert_location("//\n", 1, 0, 3);
        assert_location("//\n  ", 1, 2, 5);
        assert_location("//\n  //\r  // a", 2, 6, 14);

        assert_location("/* */", 0, 5, 5);
        assert_location("/* */\n ", 1, 1, 7);
        assert_location("/* \n \r */  ", 2, 5, 11);
        // Multi-byte UTF-8 encoded char should be considered only 1 column
        assert_location("/*\u{10FFFF}*/", 0, 5, 8);
    }

    #[test]
    fn location_value() {
        fn assert_location(json: &str, expected_column: u64, expected_byte_pos: u64) {
            let mut json_reader = new_reader(json);
            json_reader.begin_array().unwrap();
            json_reader.skip_value().unwrap();
            assert_parse_error_with_byte_pos(
                Some(json),
                json_reader.peek(),
                SyntaxErrorKind::IncompleteDocument,
                &json_path![1],
                expected_column,
                expected_byte_pos,
            );
        }

        assert_location("[true,", 6, 6);
        assert_location("[false,", 7, 7);
        assert_location("[null,", 6, 6);
        assert_location("[123e1,", 7, 7);
        assert_location(r#"["","#, 4, 4);
        assert_location(r#"["\"\\\/\b\f\n\r\t\u1234","#, 26, 26);
        // Escaped line breaks should not be considered line breaks
        assert_location(r#"["\n \r","#, 9, 9);
        assert_location(r#"["\u000A \u000D","#, 17, 17);
        // Multi-byte UTF-8 encoded character should be considered single character
        assert_location("[\"\u{10FFFF}\",", 5, 8);
        // Line separator and line paragraph should not be considered line breaks
        assert_location("[\"\u{2028}\u{2029}\",", 6, 10);
        assert_location("[[],", 4, 4);
        assert_location("[[1, 2],", 8, 8);
        assert_location("[{},", 4, 4);
        assert_location(r#"[{"a": 1},"#, 10, 10);
    }

    #[test]
    fn location_malformed_name() -> TestResult {
        let mut json_reader = new_reader("{\"a\": 1, \"b\\X\": 2}");
        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name_owned()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.next_name_owned(),
            SyntaxErrorKind::UnknownEscapeSequence,
            &json_path!["a"],
            11,
        );

        Ok(())
    }

    #[test]
    fn location_skip() -> TestResult {
        let mut json_reader =
            new_reader(r#"[true, false, null, 12, "test", [], [34], {}, {"a": 1}]"#);
        json_reader.begin_array()?;

        for (item_index, column_position) in [1, 7, 14, 20, 24, 32, 36, 42, 46].iter().enumerate() {
            assert_unexpected_structure(
                json_reader.end_array(),
                UnexpectedStructureKind::MoreElementsThanExpected,
                &json_path![item_index as u32],
                *column_position,
            );
            json_reader.skip_value()?;
        }
        json_reader.end_array()?;

        let mut json_reader = new_reader(r#"{"a": 1, "b": 2}"#);
        json_reader.begin_object()?;
        assert_unexpected_structure(
            json_reader.end_object(),
            UnexpectedStructureKind::MoreElementsThanExpected,
            &json_path!["<?>"],
            1,
        );

        json_reader.skip_name()?;
        assert_unexpected_value_type(
            json_reader.next_bool(),
            ValueType::Boolean,
            ValueType::Number,
            &json_path!["a"],
            6,
        );

        json_reader.skip_value()?;

        assert_unexpected_structure(
            json_reader.end_object(),
            UnexpectedStructureKind::MoreElementsThanExpected,
            &json_path!["a"],
            9,
        );
        json_reader.skip_name()?;
        assert_unexpected_value_type(
            json_reader.next_bool(),
            ValueType::Boolean,
            ValueType::Number,
            &json_path!["b"],
            14,
        );

        json_reader.skip_value()?;

        assert_unexpected_structure(
            json_reader.next_name_owned(),
            UnexpectedStructureKind::FewerElementsThanExpected,
            &json_path!["b"],
            15,
        );
        json_reader.end_object()?;

        Ok(())
    }

    struct FewBytesReader<'a> {
        bytes: &'a [u8],
        pos: usize,
    }

    impl Read for FewBytesReader<'_> {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            if self.pos >= self.bytes.len() {
                return Ok(0);
            }
            // Always reads at most 3 bytes
            let read_count = 3.min(buf.len().min(self.bytes.len() - self.pos));
            buf[..read_count].copy_from_slice(&self.bytes[self.pos..(self.pos + read_count)]);
            self.pos += read_count;

            Ok(read_count)
        }
    }

    #[test]
    fn few_bytes_reader() -> TestResult {
        let count = READER_BUF_SIZE;
        let json = format!("[{}true]", "true,".repeat(count - 1));
        let mut json_reader = JsonStreamReader::new(FewBytesReader {
            bytes: json.as_bytes(),
            pos: 0,
        });

        json_reader.begin_array()?;
        for _ in 0..count {
            assert_eq!(true, json_reader.next_bool()?);
        }
        json_reader.end_array()?;
        json_reader.consume_trailing_whitespace()?;
        Ok(())
    }

    #[test]
    fn large_document() -> TestResult {
        let count = READER_BUF_SIZE;
        let json = format!("[{}true]", "true,".repeat(count - 1));
        let mut json_reader = new_reader(&json);

        json_reader.begin_array()?;
        for _ in 0..count {
            assert_eq!(true, json_reader.next_bool()?);
        }
        json_reader.end_array()?;
        assert_eq!(json.len() as u64, json_reader.column);
        json_reader.consume_trailing_whitespace()?;
        Ok(())
    }

    #[test]
    fn no_path_tracking() -> TestResult {
        let mut json_reader = JsonStreamReader::new_custom(
            // Test with JSON data containing various values and a malformed `@` at the end
            "[{\"a\": [[], [1], {}, {\"b\": 1}, {\"c\": 2}, {\"d\": 3}, @]}]".as_bytes(),
            ReaderSettings {
                track_path: false,
                ..Default::default()
            },
        );
        json_reader.begin_array()?;
        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name_owned()?);
        json_reader.begin_array()?;

        json_reader.begin_array()?;
        json_reader.end_array()?;

        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        json_reader.end_array()?;

        json_reader.begin_object()?;
        json_reader.end_object()?;

        json_reader.begin_object()?;
        assert_eq!("b", json_reader.next_name_owned()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        json_reader.end_object()?;

        json_reader.begin_object()?;
        assert_eq!("c", json_reader.next_name()?);
        assert_eq!("2", json_reader.next_number_as_string()?);
        json_reader.end_object()?;

        json_reader.skip_value()?;
        match json_reader.peek() {
            Err(ReaderError::SyntaxError(JsonSyntaxError {
                kind: SyntaxErrorKind::MalformedJson,
                location:
                    JsonReaderPosition {
                        // `None` because path tracking is disabled
                        path: None,
                        line_pos:
                            Some(LinePosition {
                                line: 0,
                                column: 51,
                            }),
                        data_pos: Some(51),
                    },
            })) => {}
            r => panic!("Unexpected result: {r:?}"),
        }

        Ok(())
    }

    /// Reader which returns `ErrorKind::Interrupted` most of the time
    struct InterruptedReader<'a> {
        remaining_data: &'a [u8],
        // For every read attempt return `ErrorKind::Interrupted` a few times before performing read
        interrupted_count: u32,
    }
    impl<'a> InterruptedReader<'a> {
        pub fn new(json: &'a str) -> Self {
            InterruptedReader {
                remaining_data: json.as_bytes(),
                interrupted_count: 0,
            }
        }
    }
    impl Read for InterruptedReader<'_> {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            if self.remaining_data.is_empty() || buf.is_empty() {
                return Ok(0);
            }

            if self.interrupted_count >= 3 {
                self.interrupted_count = 0;
                // Only read a single byte
                buf[0] = self.remaining_data[0];
                self.remaining_data = &self.remaining_data[1..];
                Ok(1)
            } else {
                self.interrupted_count += 1;
                Err(IoError::from(ErrorKind::Interrupted))
            }
        }
    }

    /// String value reader must not return (or rather propagate) `ErrorKind::Interrupted`;
    /// otherwise most `Read` methods will re-attempt the read even though the underlying
    /// JSON stream reader is in an inconsistent state (e.g. incomplete escape sequence
    /// having been consumed).
    #[test]
    fn string_reader_interrupted() -> TestResult {
        let mut reader = InterruptedReader::new("\"test \\\" \u{10FFFF}\"");
        let mut json_reader = JsonStreamReader::new(&mut reader);

        let mut string_reader = json_reader.next_string_reader()?;
        let mut buf = [0_u8; 11]; // sized to matched expected string
        match string_reader.read(&mut buf) {
            // Current implementation should have filled complete buf (this is not a requirement of `Read::read` though)
            Ok(n) => assert_eq!(buf.len(), n),
            // For current implementation no error should have occurred
            // Especially regardless of implemention, `ErrorKind::Interrupted` must not have been returned
            r => panic!("Unexpected result: {r:?}"),
        }
        assert_eq!("test \" \u{10FFFF}", std::str::from_utf8(&buf)?);
        assert_eq!(0, string_reader.read(&mut buf)?);
        drop(string_reader);

        json_reader.consume_trailing_whitespace()?;
        Ok(())
    }

    /// JSON stream reader should continuously retry reading in case underlying `Read`
    /// returns `ErrorKind::Interrupted`.
    #[test]
    fn reader_interrupted() -> TestResult {
        let mut reader = InterruptedReader::new(
            "[true, 123.4e5, \"test \\\" 1 \u{10FFFF}\", \"test \\\" 2 \u{10FFFF}\"]",
        );
        let mut json_reader = JsonStreamReader::new(&mut reader);

        json_reader.begin_array()?;
        assert_eq!(true, json_reader.next_bool()?);
        assert_eq!("123.4e5", json_reader.next_number_as_str()?);
        assert_eq!("test \" 1 \u{10FFFF}", json_reader.next_str()?);

        let mut string_reader = json_reader.next_string_reader()?;
        let mut string_buf = String::new();
        string_reader.read_to_string(&mut string_buf)?;
        drop(string_reader);
        assert_eq!("test \" 2 \u{10FFFF}", string_buf);

        json_reader.end_array()?;
        json_reader.consume_trailing_whitespace()?;
        Ok(())
    }

    struct DebuggableReader<'a> {
        bytes: &'a [u8],
        has_read: bool,
    }
    impl<'a> DebuggableReader<'a> {
        fn new(bytes: &'a [u8]) -> Self {
            DebuggableReader {
                bytes,
                has_read: false,
            }
        }
    }

    impl Read for DebuggableReader<'_> {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            if self.has_read {
                return Ok(0);
            }

            let bytes_len = self.bytes.len();

            // For simplicity of this test assume that buf is large enough
            assert!(buf.len() >= bytes_len);
            buf[..bytes_len].copy_from_slice(self.bytes);
            self.has_read = true;
            Ok(bytes_len)
        }
    }

    impl Debug for DebuggableReader<'_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "debuggable-reader")
        }
    }

    fn new_with_debuggable_reader(bytes: &[u8]) -> JsonStreamReader<DebuggableReader> {
        JsonStreamReader::new(DebuggableReader::new(bytes))
    }

    // The following Debug output tests mainly exist to make sure the buffer content is properly displayed
    // Besides that they heavily rely on implementation details

    #[test]
    fn debug_reader() -> TestResult {
        let json_number = "123";
        let mut json_reader = new_with_debuggable_reader(json_number.as_bytes());
        assert_eq!(
            "JsonStreamReader { reader: debuggable-reader, buf_count: 0, buf_str: \"\", peeked: None, is_empty: true, expects_member_name: false, stack: [], is_string_value_reader_active: false, line: 0, column: 0, byte_pos: 0, json_path: Some([]), reader_settings: ReaderSettings { allow_comments: false, allow_trailing_comma: false, allow_multiple_top_level: false, track_path: true, restrict_number_values: true } }",
            format!("{json_reader:?}")
        );

        assert_eq!(ValueType::Number, json_reader.peek()?);
        assert_eq!(
            "JsonStreamReader { reader: debuggable-reader, buf_count: 3, buf_str: \"123\", peeked: Some(NumberStart), is_empty: true, expects_member_name: false, stack: [], is_string_value_reader_active: false, line: 0, column: 0, byte_pos: 0, json_path: Some([]), reader_settings: ReaderSettings { allow_comments: false, allow_trailing_comma: false, allow_multiple_top_level: false, track_path: true, restrict_number_values: true } }",
            format!("{json_reader:?}")
        );

        assert_eq!(json_number, json_reader.next_number_as_string()?);
        json_reader.consume_trailing_whitespace()?;
        Ok(())
    }

    #[test]
    fn debug_reader_long() -> TestResult {
        let json_number = "123456".repeat(100);
        let mut json_reader = JsonStreamReader::new_custom(
            DebuggableReader::new(json_number.as_bytes()),
            ReaderSettings {
                restrict_number_values: false,
                ..Default::default()
            },
        );

        assert_eq!(ValueType::Number, json_reader.peek()?);
        assert_eq!(
            "JsonStreamReader { reader: debuggable-reader, buf_count: 600, buf_str: \"123456123456123456123456123456123456123456123...\", peeked: Some(NumberStart), is_empty: true, expects_member_name: false, stack: [], is_string_value_reader_active: false, line: 0, column: 0, byte_pos: 0, json_path: Some([]), reader_settings: ReaderSettings { allow_comments: false, allow_trailing_comma: false, allow_multiple_top_level: false, track_path: true, restrict_number_values: false } }",
            format!("{json_reader:?}")
        );

        assert_eq!(json_number, json_reader.next_number_as_string()?);
        json_reader.consume_trailing_whitespace()?;
        Ok(())
    }

    #[test]
    fn debug_reader_incomplete() -> TestResult {
        // Incomplete UTF-8 multi-byte
        let json = b"\"this is a test\xC3";
        let mut json_reader = new_with_debuggable_reader(json);
        assert_eq!(ValueType::String, json_reader.peek()?);
        assert_eq!(
            "JsonStreamReader { reader: debuggable-reader, buf_count: 15, buf_str: \"this is a test...\", ...buf...: [195], peeked: Some(StringStart), is_empty: true, expects_member_name: false, stack: [], is_string_value_reader_active: false, line: 0, column: 0, byte_pos: 0, json_path: Some([]), reader_settings: ReaderSettings { allow_comments: false, allow_trailing_comma: false, allow_multiple_top_level: false, track_path: true, restrict_number_values: true } }",
            format!("{json_reader:?}")
        );
        Ok(())
    }

    #[test]
    fn debug_reader_invalid_short() -> TestResult {
        // Malformed UTF-8
        let json = b"\"a\xFF";
        let mut json_reader = new_with_debuggable_reader(json);
        assert_eq!(ValueType::String, json_reader.peek()?);
        assert_eq!(
            "JsonStreamReader { reader: debuggable-reader, buf_count: 2, buf_str: \"a...\", ...buf...: [255], peeked: Some(StringStart), is_empty: true, expects_member_name: false, stack: [], is_string_value_reader_active: false, line: 0, column: 0, byte_pos: 0, json_path: Some([]), reader_settings: ReaderSettings { allow_comments: false, allow_trailing_comma: false, allow_multiple_top_level: false, track_path: true, restrict_number_values: true } }",
            format!("{json_reader:?}")
        );
        Ok(())
    }

    #[test]
    fn debug_reader_invalid_long() -> TestResult {
        // Malformed UTF-8 after long valid prefix
        let mut json = vec![b'\"'];
        json.extend(b"abcdef".repeat(20));
        json.push(b'\xFF');

        let mut json_reader = new_with_debuggable_reader(json.as_slice());
        assert_eq!(ValueType::String, json_reader.peek()?);
        assert_eq!(
            "JsonStreamReader { reader: debuggable-reader, buf_count: 121, buf_str: \"abcdefabcdefabcdefabcdefabcdefabcdefabcdefabc...\", peeked: Some(StringStart), is_empty: true, expects_member_name: false, stack: [], is_string_value_reader_active: false, line: 0, column: 0, byte_pos: 0, json_path: Some([]), reader_settings: ReaderSettings { allow_comments: false, allow_trailing_comma: false, allow_multiple_top_level: false, track_path: true, restrict_number_values: true } }",
            format!("{json_reader:?}")
        );
        Ok(())
    }

    #[test]
    fn large_number() -> TestResult {
        let count = READER_BUF_SIZE;
        let number_json = "123".repeat(count);
        let mut json_reader = JsonStreamReader::new_custom(
            number_json.as_bytes(),
            ReaderSettings {
                restrict_number_values: false,
                ..Default::default()
            },
        );

        assert_eq!(number_json, json_reader.next_number_as_string()?);
        assert_eq!(number_json.len() as u64, json_reader.column);
        json_reader.consume_trailing_whitespace()?;
        Ok(())
    }

    #[test]
    fn large_string() -> TestResult {
        let count = READER_BUF_SIZE;
        let string_json = "abc\u{10FFFF}d\\u1234e\\n".repeat(count);
        let expected_string_value = "abc\u{10FFFF}d\u{1234}e\n".repeat(count);
        let json = format!("\"{string_json}\"");
        let mut json_reader = new_reader(&json);

        assert_eq!(expected_string_value, json_reader.next_string()?);
        // `- (3 * count)` to account for \u{10FFFF} taking up 4 bytes but representing a single char
        assert_eq!((json.len() - (3 * count)) as u64, json_reader.column);
        json_reader.consume_trailing_whitespace()?;
        Ok(())
    }

    #[cfg(feature = "serde")]
    mod serde {
        use super::*;
        use crate::serde::DeserializerError;
        use ::serde::Deserialize;
        use std::{collections::HashMap, vec};

        #[test]
        fn deserialize_next() -> TestResult {
            let mut json_reader = new_reader(r#"{"a": 5, "b":{"key": "value"}, "c": [1, 2]}"#);

            #[derive(Deserialize, PartialEq, Debug)]
            struct CustomStruct {
                a: u64,
                b: HashMap<String, String>,
                c: Vec<i32>,
            }
            let value = json_reader.deserialize_next()?;
            json_reader.consume_trailing_whitespace()?;

            assert_eq!(
                CustomStruct {
                    a: 5,
                    b: HashMap::from([("key".to_owned(), "value".to_owned())]),
                    c: vec![1, 2]
                },
                value
            );

            Ok(())
        }

        #[test]
        fn deserialize_next_invalid() {
            let mut json_reader = new_reader("true");
            match json_reader.deserialize_next::<u64>() {
                Err(DeserializerError::ReaderError(ReaderError::UnexpectedValueType {
                    expected,
                    actual,
                    location,
                })) => {
                    assert_eq!(ValueType::Number, expected);
                    assert_eq!(ValueType::Boolean, actual);
                    assert_eq!(
                        JsonReaderPosition {
                            path: Some(Vec::new()),
                            line_pos: Some(LinePosition { line: 0, column: 0 }),
                            data_pos: Some(0),
                        },
                        location
                    );
                }
                r => panic!("Unexpected result: {r:?}"),
            }
        }

        #[test]
        #[should_panic(
            expected = "Incorrect reader usage: Cannot peek value when expecting member name"
        )]
        fn deserialize_next_no_value_expected() {
            let mut json_reader = new_reader(r#"{"a": 1}"#);
            json_reader.begin_object().unwrap();

            json_reader.deserialize_next::<String>().unwrap();
        }
    }
}
