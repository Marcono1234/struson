//! Module for writing JSON data
//!
//! [`JsonWriter`] is the general trait for JSON writers, [`JsonStreamWriter`] is an implementation
//! of it which writes a JSON document to a [`Write`] in a streaming way.

use crate::json_number::consume_json_number;

use std::{
    fmt::Debug,
    io::{ErrorKind, Write},
    str::Utf8Error,
};

use duplicate::duplicate_item;
use thiserror::Error;

type IoError = std::io::Error;

/// A trait for JSON writers
///
/// The methods of this writer can be divided into the following categories:
///
/// - Writing values
///     - [`begin_array`](Self::begin_array), [`end_array`](Self::end_array): Starting and ending a JSON array
///     - [`begin_object`](Self::begin_object), [`end_object`](Self::end_object): Starting and ending a JSON object
///     - [`name`](Self::name): Writing a JSON object member name
///     - [`string_value`](Self::string_value), [`string_value_writer`](Self::string_value_writer): Writing a JSON string value
///     - [`number_value`](Self::number_value), [`fp_number_value`](Self::fp_number_value), [`number_value_from_string`](Self::number_value_from_string): Writing a JSON number value
///     - [`bool_value`](Self::bool_value): Writing a JSON boolean value
///     - [`null_value`](Self::null_value): Writing a JSON null value
///  - Other:
///     - [`finish_document`](Self::finish_document): Ensuring that the JSON document is complete and flushing the buffer
///
/// JSON documents have at least one top-level value which can be either a JSON array, object,
/// string, number, boolean or null value. For JSON arrays and objects the opening brackets
/// must be written with the corresponding `begin_` method (for example [`begin_array`](Self::begin_array)) and the
/// closing bracket with the corresponding `end_` method (for example [`end_array`](Self::end_array)). JSON objects
/// consist of *members* which are name-value pairs. The name of a member can be written with
/// [`name`](Self::name) and the value with any of the value writing methods such as [`bool_value`](Self::bool_value).
///
/// Once the JSON document is complete, [`finish_document`](Self::finish_document) has to be called to ensure that the
/// JSON document really is complete and to flush the internal buffer to the underlying writer.
/// Forgetting to call [`finish_document`](Self::finish_document) leads to unspecified behavior; most likely the written
/// JSON document will be incomplete.
///
/// # Examples
/// ```
/// # use ron::writer::*;
/// // In this example JSON bytes are stored in a Vec;
/// // normally they would be written to a file or network connection
/// let mut writer = Vec::<u8>::new();
/// let mut json_writer = JsonStreamWriter::new(&mut writer);
///
/// json_writer.begin_object()?;
/// json_writer.name("a")?;
///
/// json_writer.begin_array()?;
/// json_writer.number_value(1)?;
/// json_writer.bool_value(true)?;
/// json_writer.end_array()?;
///
/// json_writer.end_object()?;
/// // Ensures that the JSON document is complete and flushes the buffer
/// json_writer.finish_document()?;
///
/// assert_eq!(r#"{"a":[1,true]}"#, std::str::from_utf8(&writer)?);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Error handling
/// The methods of this writer return a [`Result::Err`] when an error occurs while writing
/// the JSON document. In most cases the error can only be an IO error which was caused
/// by the underlying writer. When encountering such an error, writing the JSON document
/// **must** be aborted. Trying to call any writer methods afterwards can lead to unspecified
/// behavior.
///
/// In general it is recommended to handle errors with the `?` operator of Rust, for example
/// `json_writer.bool_value(true)?` and to abort writing the JSON document when an error occurs.
///
/// # Panics
/// Methods of this writer panic when used in an incorrect way. The documentation of the methods
/// describes in detail the situations when that will happen. In general all these cases are
/// related to incorrect usage by the user (such as trying to call [`end_object`](Self::end_object) when currently
/// writing a JSON array).
pub trait JsonWriter {
    // TODO: Should these methods all return &mut Self to allow chaining?

    /// Begins writing a JSON object
    ///
    /// To write member of the object first call [`name`](Self::name) to write the member name
    /// and afterwards one of the value writing to write the member value. At the end
    /// call [`end_object`](Self::end_object) to write the closing bracket of the JSON object.
    ///
    /// # Examples
    /// ```
    /// # use ron::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.begin_object()?;
    /// json_writer.name("a")?;
    /// json_writer.number_value(1)?;
    /// json_writer.end_object()?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// assert_eq!(r#"{"a":1}"#, std::str::from_utf8(&writer)?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not enabled in the [`WriterSettings`]. Both cases indicate incorrect
    /// usage by the user.
    fn begin_object(&mut self) -> Result<(), IoError>;

    /// Writes the closing bracket `}` of the current JSON object
    ///
    /// This method is used to end a JSON object started by [`begin_object`](Self::begin_object).
    ///
    /// # Panics
    /// Panics when called on a JSON writer which is currently not inside a JSON object,
    /// or when the value of a member is currently expected. Both cases indicate incorrect
    /// usage by the user.
    fn end_object(&mut self) -> Result<(), IoError>;

    /// Begins writing a JSON array
    ///
    /// To write items of the array the regular value writing methods such as [`number_value`](Self::number_value)
    /// can be used. At the end call [`end_array`](Self::end_array) to write the closing bracket of the JSON array.
    ///
    /// Note that JSON arrays can contain values of different types, so for example the
    /// following is valid JSON: `[1, true, "a"]`
    ///
    /// # Examples
    /// ```
    /// # use ron::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.begin_array()?;
    /// json_writer.number_value(1)?;
    /// json_writer.end_array()?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// assert_eq!("[1]", std::str::from_utf8(&writer)?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not enabled in the [`WriterSettings`]. Both cases indicate incorrect
    /// usage by the user.
    fn begin_array(&mut self) -> Result<(), IoError>;

    /// Writes the closing bracket `]` of the current JSON object
    ///
    /// This method is used to end a JSON array started by [`begin_array`](Self::begin_array).
    ///
    /// # Panics
    /// Panics when called on a JSON writer which is currently not inside a JSON array.
    /// This indicates incorrect usage by the user.
    fn end_array(&mut self) -> Result<(), IoError>;

    /// Writes the name of the next JSON object member
    ///
    /// Afterwards one of the value writing methods such as [`number_value`](Self::number_value) can be used
    /// to write the corresponding member value.
    ///
    /// This method does not detect or prevent duplicate member names, such as in
    /// `{"a": 1, "a": 2}`. Duplicate member names should be avoided because not all JSON
    /// parsers might support them, and the way they are processed might not be consistent
    /// between different JSON libraries.
    ///
    /// Characters are automatically escaped in the JSON output if necessary. For example
    /// the character U+0000 is written as `\u0000`.
    ///
    /// # Examples
    /// ```
    /// # use ron::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.begin_object()?;
    /// json_writer.name("a")?;
    /// json_writer.number_value(1)?;
    /// json_writer.end_object()?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// assert_eq!(r#"{"a":1}"#, std::str::from_utf8(&writer)?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently does not expect a member name. This
    /// indicates incorrect usage by the user.
    fn name(&mut self, name: &str) -> Result<(), IoError>;

    /// Writes a JSON null value
    ///
    /// This method takes no argument because there is only one JSON null value, which
    /// has no variants.
    ///
    /// # Examples
    /// ```
    /// # use ron::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.null_value()?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// assert_eq!("null", std::str::from_utf8(&writer)?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not enabled in the [`WriterSettings`]. Both cases indicate incorrect
    /// usage by the user.
    fn null_value(&mut self) -> Result<(), IoError>;

    /// Writes a JSON boolean value
    ///
    /// # Examples
    /// ```
    /// # use ron::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.bool_value(true)?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// assert_eq!("true", std::str::from_utf8(&writer)?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not enabled in the [`WriterSettings`]. Both cases indicate incorrect
    /// usage by the user.
    fn bool_value(&mut self, value: bool) -> Result<(), IoError>;

    /// Writes a JSON string value
    ///
    /// This method is only intended to write string values, it cannot be used to write
    /// JSON object member names. The method [`name`](Self::name) has to be used for that.
    ///
    /// To avoid having to store the complete string value in memory, the method [`string_value_writer`](Self::string_value_writer)
    /// can be used to obtain a writer which allows lazily writing the value. Especially for
    /// large string values this can be useful.
    ///
    /// Characters are automatically escaped in the JSON output if necessary. For example
    /// the character U+0000 is written as `\u0000`.
    ///
    /// # Examples
    /// ```
    /// # use ron::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.string_value("text with \"quotes\"")?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// assert_eq!(r#""text with \"quotes\"""#, std::str::from_utf8(&writer)?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not enabled in the [`WriterSettings`]. Both cases indicate incorrect
    /// usage by the user.
    fn string_value(&mut self, value: &str) -> Result<(), IoError>;

    /// Provides a writer for lazily writing a JSON string value
    ///
    /// This method is mainly designed to write large string values in a memory efficient
    /// way. If that is not a concern the method [`string_value`](Self::string_value) should be used instead.
    ///
    /// This method is only intended to write string values, it cannot be used to write
    /// JSON object member names. The method [`name`](Self::name) has to be used for that.
    ///
    /// Characters are automatically escaped in the JSON output if necessary. For example
    /// the character U+0000 is written as `\u0000`. Writing invalid UTF-8 data to the
    /// writer will cause a [`std::io::Error`].
    ///
    /// **Important:** Once the string value is finished, [`StringValueWriter::finish_value`]
    /// must be called. Otherwise the string value writer will still be considered 'active'
    /// and all methods of this JSON writer will panic.
    ///
    /// # Examples
    /// ```
    /// # use ron::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// let mut string_writer = json_writer.string_value_writer()?;
    ///
    /// string_writer.write_all("text ".as_bytes())?;
    /// string_writer.write_all(r#"with "quotes""#.as_bytes())?;
    /// // Important: Must explicitly indicate that value is finished
    /// string_writer.finish_value()?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// assert_eq!(r#""text with \"quotes\"""#, std::str::from_utf8(&writer)?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not enabled in the [`WriterSettings`]. Both cases indicate incorrect
    /// usage by the user.
    // TODO: Instead of Box<dyn ...> should this directly declare struct as return type
    //   (and not have separate trait StringValueWriter)?
    //   But then users might not be able to implement JsonWriter themselves anymore easily;
    //   would also be inconsistent with JsonReader::next_string_reader
    fn string_value_writer(&mut self) -> Result<Box<dyn StringValueWriter + '_>, IoError>;

    /// Writes the string representation of a JSON number value
    ///
    /// This method is mainly intended for custom number implementations or situations
    /// where the exact format of the JSON number is important. In all other cases either
    /// [`number_value`](Self::number_value) or [`fp_number_value`](Self::fp_number_value) should be used.
    ///
    /// # Examples
    /// ```
    /// # use ron::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.number_value_from_string("123.0e10")?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// assert_eq!("123.0e10", std::str::from_utf8(&writer)?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// Returns a [`JsonNumberError::InvalidNumber`] when the provided string is not a valid
    /// JSON number. Non-finite floating point numbers such as `NaN` or `Infinity` are not
    /// allowed by JSON and have to be written as JSON string value with [`string_value`](Self::string_value).
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not enabled in the [`WriterSettings`]. Both cases indicate incorrect
    /// usage by the user.
    fn number_value_from_string(&mut self, value: &str) -> Result<(), JsonNumberError>;

    /// Writes an integral JSON number value
    ///
    /// This method supports all standard primitive integral number types, such as `u32`.
    /// To write a floating point value use [`fp_number_value`](Self::fp_number_value), to write a number in a
    /// specific format use [`number_value_from_string`](Self::number_value_from_string).
    ///
    /// # Examples
    /// ```
    /// # use ron::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.number_value(123)?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// assert_eq!("123", std::str::from_utf8(&writer)?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not enabled in the [`WriterSettings`]. Both cases indicate incorrect
    /// usage by the user.
    fn number_value<N: IntegralNumber>(&mut self, value: N) -> Result<(), IoError>;

    /// Writes a floating point JSON number value
    ///
    /// This method supports the standard floating point number types `f32` and `f64`.
    /// To write an integral number value use [`number_value`](Self::number_value), to write a number in a
    /// specific format use [`number_value_from_string`](Self::number_value_from_string).
    ///
    /// The number is converted to a JSON number by calling `to_string` on it.
    ///
    /// # Examples
    /// ```
    /// # use ron::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.fp_number_value(4.5)?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// assert_eq!("4.5", std::str::from_utf8(&writer)?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// Returns a [`JsonNumberError::InvalidNumber`] when the provided number is non-finite.
    /// Non-finite floating point numbers such as `NaN` or `Infinity` are not
    /// allowed by JSON and have to be written as JSON string value with [`string_value`](Self::string_value).
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not enabled in the [`WriterSettings`]. Both cases indicate incorrect
    /// usage by the user.
    // TODO: Maybe give this method a better name?
    // TODO: Maybe also support writing in scientifict notation, e.g. `4.1e1`, see also https://doc.rust-lang.org/std/fmt/trait.LowerExp.html
    fn fp_number_value<N: FloatingPointNumber>(&mut self, value: N) -> Result<(), JsonNumberError>;

    /// Verifies that the JSON document is complete and flushes the buffer
    ///
    /// This method **must** be called explicitly. Dropping the JSON writer will not
    /// automatically flush the buffer.
    ///
    /// **Important:** It is expected that there is always at least one top-level value
    /// in a JSON document, so calling this method without having written a value yet
    /// will panic, see "Panics" section below.
    ///
    /// # Panics
    /// Panics when called on a JSON writer which has not written any top-level yet, or when
    /// called while the top-level value has not been fully written yet. Both cases
    /// indicate incorrect usage by the user.
    // Consumes 'self'
    // Note: Dropping writer will not automatically finish document since that would silently discard errors which might occur
    // TODO: Does consuming 'self' here really guarantee that writer cannot be used afterwards anymore; can this be bypassed with reference somehow?
    fn finish_document(self) -> Result<(), IoError>;
}

/// Writer for lazily writing a JSON string value
///
/// A string value writer can be obtained from [`JsonWriter::string_value_writer`].
///
/// Characters are automatically escaped in the JSON output if necessary. For example
/// the character U+0000 is written as `\u0000`. Writing invalid UTF-8 data will cause
/// a [`std::io::Error`].
///
/// **Important:** Once the string value is finished, [`finish_value`](StringValueWriter::finish_value) must be called.
/// Otherwise the string value writer will still be considered 'active' and all
/// methods of the original JSON writer will panic. Dropping the writer will not
/// automatically finish the value.
// Note: Dropping writer will not automatically finish value since that would silently discard errors which might occur
pub trait StringValueWriter: Write {
    /// Finishes the JSON string value
    ///
    /// This method must be called when writing the string value is done to allow
    /// using the original JSON writer again.
    // Consumes 'self'
    fn finish_value(self: Box<Self>) -> Result<(), IoError>;
}

/// Sealed trait for primitive integral number types such as `u32`
///
/// Implementing this trait for custom number types is not possible. Use the
/// method [`JsonWriter::number_value_from_string`] to write them to the JSON
/// document.
pub trait IntegralNumber: private::Sealed + ToString + Copy {
    /// Converts this to number to a JSON number string
    #[doc(hidden)]
    fn to_json_number(self) -> String {
        self.to_string()
    }
}

/// Sealed trait for primitive floating point number types such as `f64`
///
/// Implementing this trait for custom number types is not possible. Use the
/// method [`JsonWriter::number_value_from_string`] to write them to the JSON
/// document.
pub trait FloatingPointNumber: private::Sealed + ToString + Copy {
    /// Converts this to number to a JSON number string
    ///
    /// Returns an error if this number is not finite
    #[doc(hidden)]
    fn to_json_number(self) -> Result<String, JsonNumberError>;
}

mod private {
    use super::*;

    // Sealed trait, see https://rust-lang.github.io/api-guidelines/future-proofing.html#sealed-traits-protect-against-downstream-implementations-c-sealed
    pub trait Sealed {}

    // Use `duplicate` create to avoid repeating code for all supported types, see https://stackoverflow.com/a/61467564
    #[duplicate_item(type_template; [u8]; [i8]; [u16]; [i16]; [u32]; [i32]; [u64]; [i64]; [u128]; [i128]; [usize]; [isize]; [f32]; [f64])]
    impl Sealed for type_template {}
}

/// Error which occurred while writing a JSON number
#[derive(Error, Debug)]
pub enum JsonNumberError {
    /// The number is not a valid JSON number
    ///
    /// The data of this enum variant is a message explaining why the number is not valid.
    #[error("{0}")]
    InvalidNumber(String),
    /// An IO error occurred while writing the number
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
}

// Use `duplicate` create to avoid repeating code for all supported types, see https://stackoverflow.com/a/61467564
#[duplicate_item(type_template; [u8]; [i8]; [u16]; [i16]; [u32]; [i32]; [u64]; [i64]; [u128]; [i128]; [usize]; [isize])]
impl IntegralNumber for type_template {}

#[duplicate_item(type_template; [f32]; [f64])]
impl FloatingPointNumber for type_template {
    fn to_json_number(self) -> Result<String, JsonNumberError> {
        if self.is_finite() {
            Ok(self.to_string())
        } else {
            Err(JsonNumberError::InvalidNumber(
                "Non-finite number".to_owned(),
            ))
        }
    }
}

/// Settings to customize the JSON writer behavior
///
/// Except for [allowing multiple top-level values](WriterSettings::multi_top_level_value_separator) these
/// settings only have an effect on how the JSON output will look like without affecting
/// its data in any way. All compliant JSON readers should consider the data identical.
///
/// These settings are used by [`JsonStreamWriter::new_custom`].
#[derive(Clone, Debug)]
pub struct WriterSettings {
    /// Whether to pretty print the JSON output
    ///
    /// When enabled the JSON output will have spaces and line breaks to make it easier
    /// for humans to read. Otherwise the JSON output will be compact and have no whitespace.
    /// Pretty printed JSON output might for example look like this:
    /// ```json
    /// {
    ///     "a": [
    ///         1,
    ///         2
    ///     ]
    /// }
    /// ```
    /// Whereas compact JSON output would look like this:
    /// ```json
    /// {"a":[1,2]}
    /// ```
    ///
    /// This setting does not have any effect on the validity of the JSON output.
    /// Pretty printed JSON is allowed by the JSON specification.
    pub pretty_print: bool,

    /// Whether to escape all control characters
    ///
    /// The JSON specification only requires that the Unicode control characters `0x00` to `0x1F`
    /// (inclusive) must be escaped in member names and string values. When this setting
    /// is enabled additionally all Unicode characters for which [`char::is_control`] returns
    /// true will be escaped.
    ///
    /// This setting does not have any effect on the validity of the JSON output. Any
    /// character in member names and string values may be written as escape sequence.
    pub escape_all_control_chars: bool,

    /// Whether to escape all non-ASCII characters
    ///
    /// When enabled all Unicode characters in member names and string values whose code point
    /// is >= `0x80` are written as escape sequence. This can be useful when interacting with
    /// legacy systems which do not properly support non-ASCII input.
    ///
    /// This setting does not have any effect on the validity of the JSON output. Any
    /// character in member names and string values may be written as escape sequence.
    pub escape_all_non_ascii: bool,

    /// Whether to allow multiple top-level values, and if allowed which separator to use
    ///
    /// When `None` multiple top-level values are not allowed. Otherwise when `Some(...)` it
    /// specifies the seperator to use between multiple top-level values. The separator can
    /// be an arbitrary string, however there are a few things to keep in mind:
    /// - An empty string (`""`) might prevent some JSON values from being properly parsed.
    ///   For example the values `true` and `false` would be written as `truefalse` which
    ///   might not be accepted as valid JSON by some JSON reader implementations.
    /// - Using something different than regular JSON whitespace (space, `\t`, `\r` and `\n`)
    ///   might lead to output which cannot be parsed properly by some JSON reader implementations.
    ///
    /// For example, with the separator `" ### "` writing the values `123`, `true` and `[]`
    /// would yield: `123 ### true ### []`
    ///
    /// Normally a JSON document is expected to contain only a single top-level value, but there
    /// might be use cases where supporting multiple top-level values can be useful.
    pub multi_top_level_value_separator: Option<String>,
}

impl Default for WriterSettings {
    /// Creates the default JSON writer settings
    ///
    /// - pretty print: disabled (= compact JSON will be written)
    /// - escape all control chars: false (= only control characters `0x00` to `0x1F` are escaped)
    /// - multiple top level values: disallowed
    fn default() -> Self {
        WriterSettings {
            pretty_print: false,
            escape_all_control_chars: false,
            escape_all_non_ascii: false,
            multi_top_level_value_separator: None,
        }
    }
}

#[derive(PartialEq, Debug)]
enum StackValue {
    Array,
    Object,
}

const WRITER_BUF_SIZE: usize = 1024;

/// A JSON writer implementation which writes data to a [`Write`]
///
/// This writer internally buffers data so it is normally not necessary to wrap the provided
/// writer in a [`std::io::BufWriter`].
///
/// The data written to the underlying writer will be valid UTF-8 data if the JSON document
/// is finished properly by calling [`JsonWriter::finish_document`]. No leading byte order mark (BOM)
/// is written.
pub struct JsonStreamWriter<W: Write> {
    // When adding more fields to this struct, adjust the Debug implementation below, if necessary
    writer: W,
    buf: [u8; WRITER_BUF_SIZE],
    /// Index (starting at 0) within [`buf`](Self::buf) where to write next,
    /// respectively how many bytes have already been written to the buffer
    buf_write_pos: usize,
    /// Whether the current array or object is empty, or at top-level whether
    /// at least one value has been written already
    is_empty: bool,
    expects_member_name: bool,
    stack: Vec<StackValue>,
    is_string_value_writer_active: bool,
    indentation_level: u32,

    writer_settings: WriterSettings,
}

impl<W: Write> JsonStreamWriter<W> {
    /// Creates a JSON writer with [default settings](WriterSettings::default)
    pub fn new(writer: W) -> Self {
        JsonStreamWriter::new_custom(writer, WriterSettings::default())
    }

    /// Creates a JSON writer with custom settings
    ///
    /// The settings can be used to customize how the JSON output will look like.
    pub fn new_custom(writer: W, writer_settings: WriterSettings) -> Self {
        Self {
            writer,
            buf: [0; WRITER_BUF_SIZE],
            buf_write_pos: 0,
            is_empty: true,
            expects_member_name: false,
            stack: Vec::new(),
            is_string_value_writer_active: false,
            indentation_level: 0,
            writer_settings,
        }
    }

    fn should_escape(&self, c: char) -> bool {
        c == '"' || c == '\\'
        // Control characters which must be escaped per JSON specification
        || ('\u{0}'..='\u{1F}').contains(&c)
            || (self.writer_settings.escape_all_non_ascii && !c.is_ascii())
            || (self.writer_settings.escape_all_control_chars && c.is_control())
    }

    fn write_escaped_char(&mut self, c: char) -> Result<(), IoError> {
        let escape = match c {
            '"' => "\\\"",
            '\\' => "\\\\",
            '/' => "\\/",
            '\u{0008}' => "\\b",
            '\u{000C}' => "\\f",
            '\n' => "\\n",
            '\r' => "\\r",
            '\t' => "\\t",
            '\0'..='\u{FFFF}' => {
                self.write_bytes(format!("\\u{:04X}", c as u32).as_bytes())?;
                return Ok(());
            }
            _ => {
                // Encode as surrogate pair
                let temp = (c as u32) - 0x10000;
                let high = (temp >> 10) + 0xD800;
                let low = (temp & ((1 << 10) - 1)) + 0xDC00;
                self.write_bytes(format!("\\u{:04X}\\u{:04X}", high, low).as_bytes())?;
                return Ok(());
            }
        };
        self.write_bytes(escape.as_bytes())?;
        Ok(())
    }

    fn write_bytes(&mut self, bytes: &[u8]) -> Result<(), IoError> {
        let mut pos = 0;
        while pos < bytes.len() {
            let copied_count = (self.buf.len() - self.buf_write_pos).min(bytes.len() - pos);
            self.buf[self.buf_write_pos..(self.buf_write_pos + copied_count)]
                .copy_from_slice(&bytes[pos..(pos + copied_count)]);
            self.buf_write_pos += copied_count;
            pos += copied_count;

            if self.buf_write_pos >= self.buf.len() {
                self.writer.write_all(&self.buf)?;
                self.buf_write_pos = 0;
            }
        }

        Ok(())
    }

    fn flush(&mut self) -> Result<(), IoError> {
        self.writer.write_all(&self.buf[0..self.buf_write_pos])?;
        self.buf_write_pos = 0;
        self.writer.flush()?;
        Ok(())
    }

    fn is_in_array(&self) -> bool {
        self.stack.last().map_or(false, |v| v == &StackValue::Array)
    }

    fn is_in_object(&self) -> bool {
        self.stack
            .last()
            .map_or(false, |v| v == &StackValue::Object)
    }

    fn increase_indentation(&mut self) {
        self.indentation_level += 1;
    }

    fn decrease_indentation(&mut self) {
        self.indentation_level -= 1;
    }

    fn write_indentation(&mut self) -> Result<(), IoError> {
        for _ in 0..self.indentation_level {
            self.write_bytes(b"  ")?;
        }
        Ok(())
    }

    fn before_container_element(&mut self) -> Result<(), IoError> {
        if self.is_empty {
            if self.writer_settings.pretty_print {
                // Convert "[" (respectively "{") to "[\n..."
                self.write_bytes(b"\n")?;
                self.increase_indentation();
                self.write_indentation()?;
            }
        } else {
            #[allow(clippy::collapsible_else_if)]
            if self.writer_settings.pretty_print {
                self.write_bytes(b",\n")?;
                self.write_indentation()?;
            } else {
                self.write_bytes(b",")?;
            }
        }
        Ok(())
    }

    fn before_value(&mut self) -> Result<(), IoError> {
        if self.is_string_value_writer_active {
            panic!("Incorrect writer usage: Cannot finish document when string value writer is still active");
        }
        if self.expects_member_name {
            panic!("Incorrect writer usage: Cannot write value when name is expected");
        }

        let is_behind_top_level = !self.is_empty && self.stack.is_empty();
        if is_behind_top_level {
            match &self.writer_settings.multi_top_level_value_separator {
                None => panic!("Incorrect writer usage: Cannot write multiple top-level values when not enabled in writer settings"),
                Some(separator) => {
                    let separator = separator.as_bytes();
                    // Workaround to allow borrowing immutable separator while at the same time `write_bytes` has a mutable borrow
                    // TODO Check if there is a saner solution to this
                    unsafe {
                        self.write_bytes(std::slice::from_raw_parts(separator.as_ptr(), separator.len()))?;
                    }
                },
            }
        } else if self.is_in_array() {
            self.before_container_element()?;
        }
        self.is_empty = false;

        if self.is_in_object() {
            // After this value a name will be expected
            self.expects_member_name = true;
        }

        Ok(())
    }

    fn on_container_end(&mut self) -> Result<(), IoError> {
        self.stack.pop();

        if !self.is_empty && self.writer_settings.pretty_print {
            self.write_bytes(b"\n")?;
            self.decrease_indentation();
            self.write_indentation()?;
        }

        // Enclosing container is not empty since this method call here is processing its child
        self.is_empty = false;

        // If after pop() call above currently in object, then expecting a member name
        self.expects_member_name = self.is_in_object();
        Ok(())
    }

    fn write_string_value_piece(&mut self, value: &str) -> Result<(), IoError> {
        let bytes = value.as_bytes();
        let mut next_to_write_index = 0;

        for (index, char) in value.char_indices() {
            if self.should_escape(char) {
                if index > next_to_write_index {
                    self.write_bytes(&bytes[next_to_write_index..index])?;
                }
                self.write_escaped_char(char)?;
                next_to_write_index = index + char.len_utf8();
            }
        }
        // Write remaining bytes
        if next_to_write_index < bytes.len() {
            self.write_bytes(&bytes[next_to_write_index..])?;
        }

        Ok(())
    }

    fn write_string_value(&mut self, value: &str) -> Result<(), IoError> {
        self.write_bytes(b"\"")?;
        self.write_string_value_piece(value)?;
        self.write_bytes(b"\"")?;
        Ok(())
    }
}

impl<W: Write> JsonWriter for JsonStreamWriter<W> {
    fn begin_object(&mut self) -> Result<(), IoError> {
        self.before_value()?;
        self.stack.push(StackValue::Object);
        self.is_empty = true;
        self.expects_member_name = true;
        self.write_bytes(b"{")?;

        Ok(())
    }

    fn name(&mut self, name: &str) -> Result<(), IoError> {
        if !self.expects_member_name {
            panic!("Incorrect writer usage: Cannot write name when name is not expected");
        }
        if self.is_string_value_writer_active {
            panic!("Incorrect writer usage: Cannot finish document when string value writer is still active");
        }
        self.before_container_element()?;
        self.write_string_value(name)?;
        self.write_bytes(if self.writer_settings.pretty_print {
            b": "
        } else {
            b":"
        })?;
        self.expects_member_name = false;

        Ok(())
    }

    fn end_object(&mut self) -> Result<(), IoError> {
        if !self.is_in_object() {
            panic!("Incorrect writer usage: Cannot end object when not inside object");
        }
        if self.is_string_value_writer_active {
            panic!("Incorrect writer usage: Cannot end object when string value writer is still active");
        }
        if !self.expects_member_name {
            panic!("Incorrect writer usage: Cannot end object when member value is expected");
        }
        self.on_container_end()?;
        self.write_bytes(b"}")?;
        Ok(())
    }

    fn begin_array(&mut self) -> Result<(), IoError> {
        self.before_value()?;
        self.stack.push(StackValue::Array);
        self.is_empty = true;

        // Clear this because it is only relevant for objects; will be restored when entering parent object (if any) again
        self.expects_member_name = false;

        self.write_bytes(b"[")?;

        Ok(())
    }

    fn end_array(&mut self) -> Result<(), IoError> {
        if !self.is_in_array() {
            panic!("Incorrect writer usage: Cannot end array when not inside array");
        }
        if self.is_string_value_writer_active {
            panic!(
                "Incorrect writer usage: Cannot end array when string value writer is still active"
            );
        }
        self.on_container_end()?;
        self.write_bytes(b"]")?;
        Ok(())
    }

    fn string_value(&mut self, value: &str) -> Result<(), IoError> {
        self.before_value()?;
        self.write_string_value(value)?;
        Ok(())
    }

    fn bool_value(&mut self, value: bool) -> Result<(), IoError> {
        self.before_value()?;
        self.write_bytes(if value { b"true" } else { b"false" })?;
        Ok(())
    }

    fn null_value(&mut self) -> Result<(), IoError> {
        self.before_value()?;
        self.write_bytes(b"null")?;
        Ok(())
    }

    fn number_value<N: IntegralNumber>(&mut self, value: N) -> Result<(), IoError> {
        self.before_value()?;
        self.write_bytes(value.to_json_number().as_bytes())?;
        Ok(())
    }

    fn fp_number_value<N: FloatingPointNumber>(&mut self, value: N) -> Result<(), JsonNumberError> {
        let number_str = value.to_json_number()?;

        self.before_value()?;
        self.write_bytes(number_str.as_bytes())?;
        Ok(())
    }

    fn number_value_from_string(&mut self, value: &str) -> Result<(), JsonNumberError> {
        if is_valid_json_number(value) {
            self.before_value()?;
            self.write_bytes(value.as_bytes())?;
            Ok(())
        } else {
            Err(JsonNumberError::InvalidNumber(
                "Invalid JSON number: ".to_owned() + value,
            ))
        }
    }

    fn finish_document(mut self) -> Result<(), IoError> {
        if self.is_string_value_writer_active {
            panic!("Incorrect writer usage: Cannot finish document when string value writer is still active");
        }
        if self.expects_member_name {
            panic!("Incorrect writer usage: Cannot finish document when member name is expected");
        }
        if self.stack.is_empty() {
            if self.is_empty {
                panic!("Incorrect writer usage: Cannot finish document when no value has been written yet");
            }
        } else {
            panic!("Incorrect writer usage: Cannot finish document when top-level value is not finished");
        }
        self.flush()?;

        Ok(())
    }

    fn string_value_writer(&mut self) -> Result<Box<dyn StringValueWriter + '_>, IoError> {
        self.before_value()?;
        self.write_bytes(b"\"")?;
        self.is_string_value_writer_active = true;
        Ok(Box::new(StringValueWriterImpl {
            json_writer: self,
            utf8_buf: [0; MAX_UTF8_BYTES_COUNT],
            utf8_pos: 0,
            utf8_expected_len: 0,
        }))
    }
}

// TODO: Is there a way to have `W` only optionally implement `Debug`?
impl<W: Write + Debug> Debug for JsonStreamWriter<W> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug_struct = f.debug_struct("JsonStreamWriter");
        debug_struct
            .field("writer", &self.writer)
            .field("buf_count", &self.buf_write_pos);

        fn limit_str_middle(s: &str) -> String {
            let chars_count = s.chars().count();

            let prefix_len = 25;
            let suffix_len = prefix_len;

            let max_len = 55;
            // Assert that `max_len` is large enough for splitting to be possible and worth it
            assert!(max_len > prefix_len + suffix_len);

            if chars_count <= max_len {
                return s.to_owned();
            }

            let prefix_end = s.char_indices().nth(prefix_len).unwrap().0;
            let prefix = &s[..prefix_end];

            // `suffix_len - 1` because `nth_back(0)` already returns inclusive index of first char
            let suffix_start = s.char_indices().nth_back(suffix_len - 1).unwrap().0;
            let suffix = &s[suffix_start..];

            format!("{prefix} ... {suffix}")
        }

        match std::str::from_utf8(&self.buf[..self.buf_write_pos]) {
            Ok(buf_string) => {
                debug_struct.field("buf_str", &limit_str_middle(buf_string));
            }
            // In case of error buffer was likely already flushed before and split valid UTF-8;
            // loop until start of next valid substring is found
            Err(_) => {
                let mut substring_start = self.buf_write_pos;
                let mut buf_string_suffix = None;

                for i in 1..self.buf_write_pos {
                    if let Ok(suffix) = std::str::from_utf8(&self.buf[i..self.buf_write_pos]) {
                        buf_string_suffix = Some(format!("...{}", &limit_str_middle(suffix)));
                        substring_start = i;
                        break;
                    }
                }

                // Only include the bytes which could not be decoded to string
                debug_struct.field("buf...", &&self.buf[..substring_start]);

                // If no valid suffix could be decoded use "..."
                debug_struct.field(
                    "buf_str",
                    &buf_string_suffix.unwrap_or_else(|| "...".to_owned()),
                );
            }
        }

        debug_struct
            .field("is_empty", &self.is_empty)
            .field("expects_member_name", &self.expects_member_name)
            .field("stack", &self.stack)
            .field(
                "is_string_value_writer_active",
                &self.is_string_value_writer_active,
            )
            .field("indentation_level", &self.indentation_level)
            .field("writer_settings", &self.writer_settings)
            .finish()
    }
}

const MAX_UTF8_BYTES_COUNT: usize = 4;

struct StringValueWriterImpl<'j, W: Write> {
    json_writer: &'j mut JsonStreamWriter<W>,
    /// Buffer used to store incomplete data of a UTF-8 multi-byte character provided by
    /// a user of this writer
    ///
    /// Buffering it is necessary to make sure it is valid UTF-8 data before writing it to the
    /// underlying `Write`.
    utf8_buf: [u8; MAX_UTF8_BYTES_COUNT],
    /// Index (0-based) within [utf8_buf] where the next byte should be written, respectively
    /// number of already written bytes
    utf8_pos: usize,
    /// Expected number of total bytes for the character whose bytes are currently in [utf8_buf]
    utf8_expected_len: usize,
}

fn map_utf8_error(e: Utf8Error) -> IoError {
    IoError::new(ErrorKind::InvalidData, e)
}

fn decode_utf8_char(bytes: &[u8]) -> Result<&str, IoError> {
    match std::str::from_utf8(bytes) {
        Err(e) => Err(map_utf8_error(e)),
        Ok(s) => {
            debug_assert!(s.chars().count() == 1);
            Ok(s)
        }
    }
}

impl<'j, W: Write> Write for StringValueWriterImpl<'j, W> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        if buf.is_empty() {
            return Ok(0);
        }

        let mut start_pos = 0;
        if self.utf8_pos > 0 {
            let copy_count = (self.utf8_expected_len - self.utf8_pos).min(buf.len());
            self.utf8_buf[self.utf8_pos..(self.utf8_pos + copy_count)]
                .copy_from_slice(&buf[..copy_count]);
            self.utf8_pos += copy_count;

            if self.utf8_pos >= self.utf8_expected_len {
                self.utf8_pos = 0;
                let s = decode_utf8_char(&self.utf8_buf[..self.utf8_expected_len])?;
                self.json_writer.write_string_value_piece(s)?;
            }
            start_pos += copy_count;
        }

        fn max_or_offset_negative(a: usize, b: usize, b_neg_off: usize) -> usize {
            debug_assert!(b >= a);
            // Avoids numeric underflow compared to normal `a.max(b - b_neg_off)`
            if b_neg_off > b {
                a
            } else {
                b - b_neg_off
            }
        }

        // Checks for incomplete UTF-8 data and converts the bytes with str::from_utf8
        let mut i = max_or_offset_negative(start_pos, buf.len(), MAX_UTF8_BYTES_COUNT);
        while i < buf.len() {
            let byte = buf[i];

            if byte > 0x7F {
                let expected_bytes_count;
                if (byte & 0b1110_0000) == 0b1100_0000 {
                    expected_bytes_count = 2;
                } else if (byte & 0b1111_0000) == 0b1110_0000 {
                    expected_bytes_count = 3;
                } else if (byte & 0b1111_1000) == 0b1111_0000 {
                    expected_bytes_count = 4;
                } else if (byte & 0b1100_0000) == 0b1000_0000 {
                    // Matched UTF-8 multi-byte continuation byte (10xxx_xxxx); continue to find start of next byte
                    i += 1;
                    continue;
                } else {
                    return Err(IoError::new(ErrorKind::InvalidData, "invalid UTF-8 data"));
                }

                let remaining_count = buf.len() - i;
                if remaining_count < expected_bytes_count {
                    self.json_writer.write_string_value_piece(
                        std::str::from_utf8(&buf[start_pos..i]).map_err(map_utf8_error)?,
                    )?;

                    // Store the incomplete UTF-8 bytes in buffer
                    self.utf8_expected_len = expected_bytes_count;
                    self.utf8_pos = remaining_count;
                    self.utf8_buf[..remaining_count].copy_from_slice(&buf[i..]);
                    return Ok(buf.len());
                } else {
                    // Skip over the bytes; - 1 because loop iteration will perfrom + 1
                    i += expected_bytes_count - 1;
                }
            }
            // Otherwise it is an ASCII char, so continue with next char
            i += 1;
        }

        self.json_writer.write_string_value_piece(
            std::str::from_utf8(&buf[start_pos..]).map_err(map_utf8_error)?,
        )?;
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.json_writer.flush()?;
        Ok(())
    }
}

impl<'j, W: Write> StringValueWriter for StringValueWriterImpl<'j, W> {
    fn finish_value(self: Box<Self>) -> Result<(), IoError> {
        if self.utf8_pos > 0 {
            return Err(IoError::new(
                ErrorKind::InvalidData,
                "incomplete multi-byte UTF-8 data",
            ));
        }
        self.json_writer.write_bytes(b"\"")?;
        self.json_writer.is_string_value_writer_active = false;
        Ok(())
    }
}

fn is_valid_json_number(value: &str) -> bool {
    if value.is_empty() {
        return false;
    }

    let value_bytes = value.as_bytes();
    let mut index = 0;
    let is_valid = consume_json_number(
        &mut || {
            index += 1;
            if index < value_bytes.len() {
                Ok::<_, ()>(Some(value_bytes[index]))
            } else {
                Ok(None)
            }
        },
        &mut |_| {},
        value_bytes[0],
    )
    .unwrap();
    // Is valid and complete string was consumed
    is_valid && index >= value_bytes.len()
}

#[cfg(test)]
mod tests {
    use std::fmt::Display;

    use super::*;

    #[test]
    fn numbers_strings() {
        fn assert_valid_number<T: IntegralNumber + Display>(number: T) {
            assert_eq!(
                true,
                is_valid_json_number(number.to_json_number().as_str()),
                "Expected to be valid JSON number: {}",
                number
            );
        }

        assert_valid_number(i8::MIN);
        assert_valid_number(i8::MAX);
        assert_valid_number(u8::MAX);

        assert_valid_number(i128::MIN);
        assert_valid_number(i128::MAX);
        assert_valid_number(u128::MAX);

        assert_valid_number(isize::MIN);
        assert_valid_number(isize::MAX);
        assert_valid_number(usize::MAX);

        fn assert_valid_fp_number<T: FloatingPointNumber + Display>(number: T) {
            assert_eq!(
                true,
                is_valid_json_number(number.to_json_number().unwrap().as_str()),
                "Expected to be valid JSON number: {}",
                number
            );
        }

        assert_valid_fp_number(f32::MIN);
        assert_valid_fp_number(f32::MIN_POSITIVE);
        assert_valid_fp_number(-f32::MIN_POSITIVE);
        assert_valid_fp_number(f32::MAX);

        assert_valid_fp_number(f64::MIN);
        assert_valid_fp_number(f64::MIN_POSITIVE);
        assert_valid_fp_number(-f64::MIN_POSITIVE);
        assert_valid_fp_number(f64::MAX);

        fn assert_non_finite<T: FloatingPointNumber + Display>(number: T) {
            match number.to_json_number() {
                Ok(_) => panic!("Should have failed for: {number}"),
                Err(e) => match e {
                    JsonNumberError::InvalidNumber(message) => {
                        assert_eq!("Non-finite number", message)
                    }
                    JsonNumberError::IoError(e) => panic!("Unexpected error for '{number}': {e}"),
                },
            }
        }

        assert_non_finite(f32::NAN);
        assert_non_finite(f32::NEG_INFINITY);
        assert_non_finite(f32::INFINITY);

        assert_non_finite(f64::NAN);
        assert_non_finite(f64::NEG_INFINITY);
        assert_non_finite(f64::INFINITY);
    }

    #[test]
    fn number_validation() {
        assert!(is_valid_json_number("0"));
        assert!(is_valid_json_number("-0"));
        assert!(is_valid_json_number("1230.1"));
        assert!(is_valid_json_number("1.01e1"));
        assert!(is_valid_json_number("12.120e+01"));
        assert!(is_valid_json_number("12.120e-10"));

        assert_eq!(false, is_valid_json_number("00"));
        assert_eq!(false, is_valid_json_number("-00"));
        assert_eq!(false, is_valid_json_number("+1"));
        assert_eq!(false, is_valid_json_number(".1"));
        assert_eq!(false, is_valid_json_number("1.-1"));
        assert_eq!(false, is_valid_json_number("1e"));
        assert_eq!(false, is_valid_json_number("1e+-1"));
        assert_eq!(false, is_valid_json_number("1e.1"));

        assert_eq!(false, is_valid_json_number("1a"));
        assert_eq!(false, is_valid_json_number("NaN"));
        assert_eq!(false, is_valid_json_number("nan"));
        assert_eq!(false, is_valid_json_number("NAN"));
        assert_eq!(false, is_valid_json_number("Infinity"));
        assert_eq!(false, is_valid_json_number("-Infinity"));
    }

    type TestResult = Result<(), Box<dyn std::error::Error>>;

    #[test]
    fn numbers() -> TestResult {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);

        json_writer.begin_array()?;
        json_writer.number_value(8_u8)?;
        json_writer.number_value(-8_i8)?;
        json_writer.number_value(16_u16)?;
        json_writer.number_value(-16_i16)?;
        json_writer.number_value(32_u32)?;
        json_writer.number_value(-32_i32)?;
        json_writer.number_value(64_u64)?;
        json_writer.number_value(-64_i64)?;
        json_writer.number_value(128_u128)?;
        json_writer.number_value(-128_i128)?;

        json_writer.fp_number_value(1.5_f32)?;
        json_writer.fp_number_value(-1.5_f32)?;
        json_writer.fp_number_value(2.5_f64)?;
        json_writer.fp_number_value(-2.5_f64)?;

        json_writer.number_value_from_string("123.45e-12")?;

        json_writer.end_array()?;
        json_writer.finish_document()?;

        assert_eq!(
            "[8,-8,16,-16,32,-32,64,-64,128,-128,1.5,-1.5,2.5,-2.5,123.45e-12]",
            std::str::from_utf8(&writer)?
        );
        Ok(())
    }

    #[test]
    fn numbers_invalid() {
        fn assert_invalid_number(result: Result<(), JsonNumberError>, expected_message: &str) {
            match result {
                Ok(_) => panic!("Should have failed"),
                Err(e) => match e {
                    JsonNumberError::InvalidNumber(message) => {
                        assert_eq!(expected_message, message)
                    }
                    JsonNumberError::IoError(e) => panic!("Unexpected error: {e}"),
                },
            }
        }

        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);

        assert_invalid_number(json_writer.fp_number_value(f32::NAN), "Non-finite number");
        assert_invalid_number(
            json_writer.fp_number_value(f64::INFINITY),
            "Non-finite number",
        );
        assert_invalid_number(
            json_writer.number_value_from_string("NaN"),
            "Invalid JSON number: NaN",
        );
        assert_invalid_number(
            json_writer.number_value_from_string("+1"),
            "Invalid JSON number: +1",
        );
        assert_invalid_number(
            json_writer.number_value_from_string("00"),
            "Invalid JSON number: 00",
        );
        assert_invalid_number(
            json_writer.number_value_from_string("1e"),
            "Invalid JSON number: 1e",
        );
        assert_invalid_number(
            json_writer.number_value_from_string("12a"),
            "Invalid JSON number: 12a",
        );
    }

    #[test]
    fn literals() -> TestResult {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_array()?;

        json_writer.bool_value(true)?;
        json_writer.bool_value(false)?;
        json_writer.null_value()?;

        json_writer.end_array()?;
        json_writer.finish_document()?;

        assert_eq!("[true,false,null]", std::str::from_utf8(&writer)?);
        Ok(())
    }

    #[test]
    fn arrays() -> TestResult {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_array()?;

        json_writer.begin_array()?;
        json_writer.number_value(1)?;
        json_writer.end_array()?;

        json_writer.begin_array()?;
        json_writer.end_array()?;

        json_writer.end_array()?;
        json_writer.finish_document()?;

        assert_eq!("[[1],[]]", std::str::from_utf8(&writer)?);
        Ok(())
    }

    #[test]
    #[should_panic(expected = "Incorrect writer usage: Cannot end array when not inside array")]
    fn end_array_not_in_array() {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_object().unwrap();

        json_writer.end_array().unwrap();
    }

    #[test]
    fn objects() -> TestResult {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_object()?;

        json_writer.name("a")?;
        json_writer.number_value(1)?;

        json_writer.name("")?;
        json_writer.number_value(2)?;

        json_writer.name("a")?;

        json_writer.begin_object()?;
        json_writer.name("c")?;
        json_writer.begin_object()?;
        json_writer.end_object()?;
        json_writer.end_object()?;

        json_writer.end_object()?;
        json_writer.finish_document()?;

        assert_eq!(
            r#"{"a":1,"":2,"a":{"c":{}}}"#,
            std::str::from_utf8(&writer)?
        );
        Ok(())
    }

    #[test]
    #[should_panic(expected = "Incorrect writer usage: Cannot end object when not inside object")]
    fn end_object_not_in_object() {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_array().unwrap();

        json_writer.end_object().unwrap();
    }

    #[test]
    #[should_panic(
        expected = "Incorrect writer usage: Cannot end object when member value is expected"
    )]
    fn end_object_expecting_value() {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_object().unwrap();
        json_writer.name("a").unwrap();

        json_writer.end_object().unwrap();
    }

    #[test]
    fn arrays_objects_mixed() -> TestResult {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_object()?;

        json_writer.name("a")?;

        json_writer.begin_object()?;
        json_writer.name("b")?;

        json_writer.begin_array()?;

        json_writer.begin_object()?;
        json_writer.end_object()?;

        json_writer.begin_object()?;
        json_writer.name("c")?;
        json_writer.begin_array()?;
        json_writer.begin_array()?;
        json_writer.end_array()?;
        json_writer.end_array()?;
        json_writer.end_object()?;

        json_writer.end_array()?;
        json_writer.name("d")?;
        json_writer.begin_array()?;
        json_writer.end_array()?;
        json_writer.end_object()?;

        json_writer.end_object()?;
        json_writer.finish_document()?;

        assert_eq!(
            r#"{"a":{"b":[{},{"c":[[]]}],"d":[]}}"#,
            std::str::from_utf8(&writer)?
        );
        Ok(())
    }

    #[test]
    fn strings() -> TestResult {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_array()?;

        json_writer.string_value("")?;
        json_writer.string_value("ab")?;
        json_writer.string_value("\u{0000}\u{001F}")?;
        json_writer.string_value("a b")?;
        json_writer.string_value("\"\\/\u{0008}\u{000C}\n\r\t")?;

        json_writer.string_value("\u{10FFFF}")?;

        json_writer.end_array()?;
        json_writer.finish_document()?;

        assert_eq!(
            r#"["","ab","\u0000\u001F","a b","\"\\/\b\f\n\r\t","#.to_owned() + "\"\u{10FFFF}\"]",
            std::str::from_utf8(&writer)?
        );
        Ok(())
    }

    #[test]
    fn string_writer() -> TestResult {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_array()?;

        let mut string_writer = json_writer.string_value_writer()?;
        assert_eq!(0, string_writer.write(b"")?);
        string_writer.write_all(b"a b")?;
        string_writer.write_all(b"\x00\x1F")?;
        string_writer.write_all(b"\"\\/\x08\x0C\n\r\t")?;
        string_writer.write_all("\u{007F}\u{10FFFF}".as_bytes())?;

        // Split bytes of multi-byte UTF-8
        let bytes = "\u{007F}\u{0080}\u{07FF}\u{0800}\u{FFFF}\u{10000}\u{10FFFF}".as_bytes();
        for b in bytes {
            string_writer.write_all(&[*b])?;
        }
        string_writer.finish_value()?;

        // Write an empty string
        let string_writer = json_writer.string_value_writer()?;
        string_writer.finish_value()?;

        json_writer.end_array()?;
        json_writer.finish_document()?;
        assert_eq!(
            r#"["a b\u0000\u001F\"\\/\b\f\n\r\t"#.to_owned()
                + "\u{007F}\u{10FFFF}\u{007F}\u{0080}\u{07FF}\u{0800}\u{FFFF}\u{10000}\u{10FFFF}\",\"\"]",
            std::str::from_utf8(&writer)?
        );
        Ok(())
    }

    #[test]
    fn string_writer_flush() -> TestResult {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);

        let mut string_writer = json_writer.string_value_writer()?;
        string_writer.write_all(b"abcd")?;
        string_writer.flush()?;
        string_writer.write_all(b"efgh")?;
        string_writer.flush()?;
        drop(string_writer);

        assert_eq!("\"abcdefgh", std::str::from_utf8(&writer)?);
        Ok(())
    }

    #[test]
    fn string_writer_invalid() {
        fn assert_invalid_utf8<
            T,
            F: FnOnce(Box<dyn StringValueWriter + '_>) -> Result<T, IoError>,
        >(
            f: F,
            expected_custom_message: Option<&str>,
        ) {
            let mut writer = Vec::<u8>::new();
            let mut json_writer = JsonStreamWriter::new(&mut writer);

            match f(json_writer.string_value_writer().unwrap()) {
                Ok(_) => panic!("Should have failed"),
                Err(e) => {
                    assert_eq!(ErrorKind::InvalidData, e.kind());

                    match expected_custom_message {
                        None => assert!(
                            e.get_ref().unwrap().is::<Utf8Error>(),
                            "Inner error is not Utf8Error"
                        ),
                        Some(message) => {
                            assert_eq!(message, e.to_string(), "Custom message does not match")
                        }
                    }
                }
            }
        }

        assert_invalid_utf8(
            |mut w| {
                // Invalid UTF-8 byte 1111_1000
                w.write_all(b"\xF8")
            },
            Some("invalid UTF-8 data"),
        );

        assert_invalid_utf8(
            |mut w| {
                // Malformed UTF-8; high surrogate U+D800 encoded in UTF-8 (= invalid)
                w.write_all(b"\xED\xA0\x80")
            },
            None,
        );

        assert_invalid_utf8(
            |mut w| {
                // Greater than max code point U+10FFFF; split across multiple bytes
                w.write_all(b"\xF4")?;
                w.write_all(b"\x90")?;
                w.write_all(b"\x80")?;
                w.write_all(b"\x80")
            },
            None,
        );

        assert_invalid_utf8(
            |mut w| {
                // Overlong encoding for two bytes
                w.write_all(b"\xC1\xBF")
            },
            None,
        );

        assert_invalid_utf8(
            |mut w| {
                // Incomplete four bytes
                w.write_all(b"\xF0")?;
                w.write_all(b"\x90")?;
                w.write_all(b"\x80")?;
                w.finish_value()
            },
            Some("incomplete multi-byte UTF-8 data"),
        );
    }

    #[test]
    #[should_panic(
        expected = "Incorrect writer usage: Cannot end array when string value writer is still active"
    )]
    fn string_writer_array_incomplete() {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_array().unwrap();

        let string_writer = json_writer.string_value_writer().unwrap();
        drop(string_writer);

        json_writer.end_array().unwrap();
    }

    #[test]
    #[should_panic(
        expected = "Incorrect writer usage: Cannot end object when string value writer is still active"
    )]
    fn string_writer_object_incomplete() {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_object().unwrap();
        json_writer.name("a").unwrap();

        let string_writer = json_writer.string_value_writer().unwrap();
        drop(string_writer);

        json_writer.end_object().unwrap();
    }

    #[test]
    #[should_panic(
        expected = "Incorrect writer usage: Cannot finish document when string value writer is still active"
    )]
    fn string_writer_incomplete_top_level() {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);

        let string_writer = json_writer.string_value_writer().unwrap();
        drop(string_writer);

        json_writer.finish_document().unwrap();
    }

    #[test]
    #[should_panic(expected = "Incorrect writer usage: Cannot write value when name is expected")]
    fn string_writer_for_name() {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_object().unwrap();

        json_writer.string_value_writer().unwrap();
    }

    #[test]
    #[should_panic(
        expected = "Incorrect writer usage: Cannot write name when name is not expected"
    )]
    fn name_as_value() {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);

        json_writer.name("test").unwrap();
    }

    #[test]
    #[should_panic(
        expected = "Incorrect writer usage: Cannot write name when name is not expected"
    )]
    fn name_as_member_value() {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_object().unwrap();
        json_writer.name("a").unwrap();

        json_writer.name("test").unwrap();
    }

    #[test]
    fn automatic_buffer_flush() -> TestResult {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.string_value("abc\"def".repeat(WRITER_BUF_SIZE).as_str())?;
        json_writer.finish_document()?;

        assert_eq!(
            "\"".to_owned() + "abc\\\"def".repeat(WRITER_BUF_SIZE).as_str() + "\"",
            std::str::from_utf8(&writer)?
        );
        Ok(())
    }

    #[test]
    fn multiple_top_level() -> TestResult {
        fn create_writer<W: Write>(writer: W, top_level_separator: &str) -> JsonStreamWriter<W> {
            JsonStreamWriter::new_custom(
                writer,
                WriterSettings {
                    pretty_print: false,
                    escape_all_control_chars: false,
                    escape_all_non_ascii: false,
                    multi_top_level_value_separator: Some(top_level_separator.to_owned()),
                },
            )
        }

        let mut writer = Vec::<u8>::new();
        let mut json_writer = create_writer(&mut writer, "");
        json_writer.begin_array()?;
        json_writer.end_array()?;
        json_writer.finish_document()?;
        assert_eq!("[]", std::str::from_utf8(&writer)?);

        let mut writer = Vec::<u8>::new();
        let mut json_writer = create_writer(&mut writer, "");
        json_writer.begin_array()?;
        json_writer.end_array()?;
        json_writer.begin_array()?;
        json_writer.end_array()?;
        json_writer.finish_document()?;
        assert_eq!("[][]", std::str::from_utf8(&writer)?);

        let mut writer = Vec::<u8>::new();
        let mut json_writer = create_writer(&mut writer, "#\n#");
        json_writer.begin_array()?;
        json_writer.end_array()?;
        json_writer.begin_array()?;
        json_writer.end_array()?;
        json_writer.finish_document()?;
        assert_eq!("[]#\n#[]", std::str::from_utf8(&writer)?);

        Ok(())
    }

    #[test]
    #[should_panic(
        expected = "Incorrect writer usage: Cannot write multiple top-level values when not enabled in writer settings"
    )]
    fn multiple_top_level_disallowed() {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.bool_value(true).unwrap();

        json_writer.bool_value(false).unwrap();
    }

    #[test]
    fn pretty_print() -> TestResult {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new_custom(
            &mut writer,
            WriterSettings {
                pretty_print: true,
                escape_all_control_chars: false,
                escape_all_non_ascii: false,
                multi_top_level_value_separator: Some("#".to_owned()),
            },
        );

        json_writer.begin_array()?;

        json_writer.begin_array()?;
        json_writer.end_array()?;

        json_writer.begin_array()?;
        json_writer.number_value(1)?;
        json_writer.end_array()?;

        json_writer.begin_object()?;

        json_writer.name("a")?;
        json_writer.begin_array()?;
        json_writer.begin_object()?;
        json_writer.name("b")?;
        json_writer.number_value(2)?;
        json_writer.end_object()?;
        json_writer.begin_object()?;
        json_writer.end_object()?;
        json_writer.end_array()?;

        json_writer.name("c")?;
        json_writer.number_value(3)?;

        json_writer.end_object()?;

        json_writer.end_array()?;

        json_writer.begin_array()?;
        json_writer.number_value(4)?;
        json_writer.end_array()?;

        json_writer.finish_document()?;

        assert_eq!("[\n  [],\n  [\n    1\n  ],\n  {\n    \"a\": [\n      {\n        \"b\": 2\n      },\n      {}\n    ],\n    \"c\": 3\n  }\n]#[\n  4\n]", std::str::from_utf8(&writer)?);
        Ok(())
    }

    #[test]
    fn escape_all_control_chars() -> TestResult {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new_custom(
            &mut writer,
            WriterSettings {
                pretty_print: false,
                escape_all_control_chars: true,
                escape_all_non_ascii: false,
                multi_top_level_value_separator: None,
            },
        );

        json_writer
            .string_value("\u{0000}\u{001F} test \" \u{007E}\u{007F}\u{0080}\u{009F}\u{00A0}")?;

        json_writer.finish_document()?;
        assert_eq!(
            "\"\\u0000\\u001F test \\\" \u{007E}\\u007F\\u0080\\u009F\u{00A0}\"",
            std::str::from_utf8(&writer)?
        );
        Ok(())
    }

    #[test]
    fn escape_all_non_ascii() -> TestResult {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new_custom(
            &mut writer,
            WriterSettings {
                pretty_print: false,
                escape_all_control_chars: false,
                escape_all_non_ascii: true,
                multi_top_level_value_separator: None,
            },
        );
        json_writer.string_value("\u{0000}\u{001F} test \" \u{007F}\u{0080}\u{10000}\u{10FFFF}")?;
        json_writer.finish_document()?;
        assert_eq!(
            "\"\\u0000\\u001F test \\\" \u{007F}\\u0080\\uD800\\uDC00\\uDBFF\\uDFFF\"",
            std::str::from_utf8(&writer)?
        );

        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new_custom(
            &mut writer,
            WriterSettings {
                pretty_print: false,
                escape_all_control_chars: true,
                escape_all_non_ascii: true,
                multi_top_level_value_separator: None,
            },
        );
        json_writer.string_value("\u{0000} test \" \u{007F}\u{0080}\u{10FFFF}")?;
        json_writer.finish_document()?;
        assert_eq!(
            "\"\\u0000 test \\\" \\u007F\\u0080\\uDBFF\\uDFFF\"",
            std::str::from_utf8(&writer)?
        );

        Ok(())
    }

    #[test]
    #[should_panic(
        expected = "Incorrect writer usage: Cannot finish document when no value has been written yet"
    )]
    fn finish_empty_document() {
        let mut writer = Vec::<u8>::new();
        let json_writer = JsonStreamWriter::new(&mut writer);

        json_writer.finish_document().unwrap();
    }

    #[test]
    #[should_panic(
        expected = "Incorrect writer usage: Cannot finish document when top-level value is not finished"
    )]
    fn finish_incomplete_document() {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_array().unwrap();

        json_writer.finish_document().unwrap();
    }

    struct DebuggableWriter;

    impl Write for DebuggableWriter {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            // Pretend complete buffer content was written
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    impl Debug for DebuggableWriter {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "debuggable-writer")
        }
    }

    fn new_with_debuggable_writer() -> JsonStreamWriter<DebuggableWriter> {
        JsonStreamWriter::new(DebuggableWriter)
    }

    // The following Debug output tests mainly exist to make sure the buffer content is properly displayed
    // Besides that they heavily rely on implementation details

    #[test]
    fn debug_writer() -> TestResult {
        let mut json_writer = new_with_debuggable_writer();
        assert_eq!(
            "JsonStreamWriter { writer: debuggable-writer, buf_count: 0, buf_str: \"\", is_empty: true, expects_member_name: false, stack: [], is_string_value_writer_active: false, indentation_level: 0, writer_settings: WriterSettings { pretty_print: false, escape_all_control_chars: false, escape_all_non_ascii: false, multi_top_level_value_separator: None } }",
            format!("{json_writer:?}")
        );

        json_writer.string_value("test")?;
        assert_eq!(
            "JsonStreamWriter { writer: debuggable-writer, buf_count: 6, buf_str: \"\\\"test\\\"\", is_empty: false, expects_member_name: false, stack: [], is_string_value_writer_active: false, indentation_level: 0, writer_settings: WriterSettings { pretty_print: false, escape_all_control_chars: false, escape_all_non_ascii: false, multi_top_level_value_separator: None } }",
            format!("{json_writer:?}")
        );
        Ok(())
    }

    #[test]
    fn debug_writer_long() -> TestResult {
        let mut json_writer = new_with_debuggable_writer();
        json_writer.string_value("test".repeat(100).as_str())?;
        assert_eq!(
            "JsonStreamWriter { writer: debuggable-writer, buf_count: 402, buf_str: \"\\\"testtesttesttesttesttest ... testtesttesttesttesttest\\\"\", is_empty: false, expects_member_name: false, stack: [], is_string_value_writer_active: false, indentation_level: 0, writer_settings: WriterSettings { pretty_print: false, escape_all_control_chars: false, escape_all_non_ascii: false, multi_top_level_value_separator: None } }",
            format!("{json_writer:?}"
        ));
        Ok(())
    }

    #[test]
    fn debug_writer_incomplete_with_suffix() -> TestResult {
        let mut json_writer = new_with_debuggable_writer();
        // Write a string value which splits a multi-byte UTF-8 char
        // `WRITER_BUF_SIZE - 2` due to leading '"' of string, and to leave one byte space for
        // first byte of multi-byte UTF-8
        let string_value = format!("{}\u{10FFFF}test", "a".repeat(WRITER_BUF_SIZE - 2));
        json_writer.string_value(&string_value)?;
        assert_eq!(
            "JsonStreamWriter { writer: debuggable-writer, buf_count: 8, buf...: [143, 191, 191], buf_str: \"...test\\\"\", is_empty: false, expects_member_name: false, stack: [], is_string_value_writer_active: false, indentation_level: 0, writer_settings: WriterSettings { pretty_print: false, escape_all_control_chars: false, escape_all_non_ascii: false, multi_top_level_value_separator: None } }",
            format!("{json_writer:?}")
        );
        Ok(())
    }

    #[test]
    fn debug_writer_incomplete_with_long_suffix() -> TestResult {
        let mut json_writer = new_with_debuggable_writer();
        // Write a string value which splits a multi-byte UTF-8 char
        // `WRITER_BUF_SIZE - 2` due to leading '"' of string, and to leave one byte space for
        // first byte of multi-byte UTF-8
        let string_value = format!(
            "{}\u{10FFFF}{}",
            "a".repeat(WRITER_BUF_SIZE - 2),
            "test".repeat(100)
        );
        json_writer.string_value(&string_value)?;
        assert_eq!(
            "JsonStreamWriter { writer: debuggable-writer, buf_count: 404, buf...: [143, 191, 191], buf_str: \"...testtesttesttesttesttestt ... testtesttesttesttesttest\\\"\", is_empty: false, expects_member_name: false, stack: [], is_string_value_writer_active: false, indentation_level: 0, writer_settings: WriterSettings { pretty_print: false, escape_all_control_chars: false, escape_all_non_ascii: false, multi_top_level_value_separator: None } }",
            format!("{json_writer:?}")
        );
        Ok(())
    }
}
