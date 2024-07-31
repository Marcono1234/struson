//! Module for writing JSON data
//!
//! [`JsonWriter`] is the general trait for JSON writers, [`JsonStreamWriter`] is an implementation
//! of it which writes a JSON document to a [`Write`] in a streaming way.

use std::{fmt::Debug, io::Write};

use duplicate::duplicate_item;
use thiserror::Error;

use crate::json_number::is_valid_json_number;

mod stream_writer;
// Re-export streaming implementation under `writer` module
pub use stream_writer::*;
#[cfg(feature = "simple-api")]
pub mod simple;

// TODO (custom JSON writer support): Remove this type alias? rust-analyzer otherwise uses that in generated
// code, even though this type alias is inaccessible, see https://github.com/rust-lang/rust-analyzer/issues/15550
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
///     - [`serialize_value`](Self::serialize_value): Serializes a Serde [`Serialize`](serde::ser::Serialize) as next value (optional feature)
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
/// JSON document will be incomplete. However, no _undefined_ behavior occurs.
///
/// # Examples
/// ```
/// # use struson::writer::*;
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
/// let json = String::from_utf8(writer)?;
/// assert_eq!(json, r#"{"a":[1,true]}"#);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Error handling
/// The methods of this writer return a [`Result::Err`] when an error occurs while writing
/// the JSON document. In most cases the error can only be an IO error which was caused
/// by the underlying writer. When encountering such an error, writing the JSON document
/// **must** be aborted. Trying to call any writer methods afterwards can lead to unspecified
/// behavior, such as errors, panics or incorrect data. However, no _undefined_ behavior occurs.
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
    /// # use struson::writer::*;
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
    /// let json = String::from_utf8(writer)?;
    /// assert_eq!(json, r#"{"a":1}"#);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not [enabled in the `WriterSettings`](WriterSettings::multi_top_level_value_separator).
    /// Both cases indicate incorrect usage by the user.
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
    /// # use struson::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.begin_array()?;
    /// json_writer.number_value(1)?;
    /// json_writer.end_array()?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// let json = String::from_utf8(writer)?;
    /// assert_eq!(json, "[1]");
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not [enabled in the `WriterSettings`](WriterSettings::multi_top_level_value_separator).
    /// Both cases indicate incorrect usage by the user.
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
    /// # use struson::writer::*;
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
    /// let json = String::from_utf8(writer)?;
    /// assert_eq!(json, r#"{"a":1}"#);
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
    /// # use struson::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.null_value()?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// let json = String::from_utf8(writer)?;
    /// assert_eq!(json, "null");
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not [enabled in the `WriterSettings`](WriterSettings::multi_top_level_value_separator).
    /// Both cases indicate incorrect usage by the user.
    fn null_value(&mut self) -> Result<(), IoError>;

    /// Writes a JSON boolean value
    ///
    /// # Examples
    /// ```
    /// # use struson::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.bool_value(true)?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// let json = String::from_utf8(writer)?;
    /// assert_eq!(json, "true");
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not [enabled in the `WriterSettings`](WriterSettings::multi_top_level_value_separator).
    /// Both cases indicate incorrect usage by the user.
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
    /// # use struson::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.string_value("text with \"quotes\"")?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// let json = String::from_utf8(writer)?;
    /// assert_eq!(json, r#""text with \"quotes\"""#);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not [enabled in the `WriterSettings`](WriterSettings::multi_top_level_value_separator).
    /// Both cases indicate incorrect usage by the user.
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
    /// the character U+0000 is written as `\u0000`.
    ///
    /// **Important:** Once the string value is finished, [`StringValueWriter::finish_value`]
    /// must be called. Otherwise the string value writer will still be considered 'active'
    /// and all methods of this JSON writer will panic.
    ///
    /// # Examples
    /// ```
    /// # use struson::writer::*;
    /// # use std::io::Write;
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
    /// let json = String::from_utf8(writer)?;
    /// assert_eq!(json, r#""text with \"quotes\"""#);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Writer errors
    /// Writing invalid UTF-8 data to the writer will cause a [`std::io::Error`].
    ///
    /// The error behavior of the string writer differs from the guarantees made by [`Write`]:
    /// - if an error is returned there are no guarantees about if or how many bytes have been
    ///   written
    /// - if an error occurs, processing should be aborted, regardless of the kind of the error;
    ///   trying to use the string writer or the underlying JSON writer afterwards will lead
    ///   to unspecified behavior
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not [enabled in the `WriterSettings`](WriterSettings::multi_top_level_value_separator).
    /// Both cases indicate incorrect usage by the user.
    fn string_value_writer(&mut self) -> Result<impl StringValueWriter + '_, IoError>;

    /// Writes the string representation of a JSON number value
    ///
    /// This method is mainly intended for custom number implementations or situations
    /// where the exact format of the JSON number is important. In all other cases either
    /// [`number_value`](Self::number_value) or [`fp_number_value`](Self::fp_number_value) should be used.
    ///
    /// # Examples
    /// ```
    /// # use struson::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.number_value_from_string("123.0e10")?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// let json = String::from_utf8(writer)?;
    /// assert_eq!(json, "123.0e10");
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
    /// values are not [enabled in the `WriterSettings`](WriterSettings::multi_top_level_value_separator).
    /// Both cases indicate incorrect usage by the user.
    /*
     * TODO (custom JSON writer support): Maybe either publicly expose function for validating
     *   that string is valid JSON number, or use wrapping struct whose constructor ensures that
     *   string is valid JSON number.
     *   Though that might make usage of the writer more cumbersome.
     * TODO: Rename to `number_string_value`?
     */
    fn number_value_from_string(&mut self, value: &str) -> Result<(), JsonNumberError>;

    /// Writes a finite JSON number value
    ///
    /// This method supports all standard primitive integral number types, such as `u32`.
    /// To write a floating point number use [`fp_number_value`](Self::fp_number_value), to write a number in a
    /// specific format use [`number_value_from_string`](Self::number_value_from_string).
    ///
    /// # Examples
    /// ```
    /// # use struson::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.number_value(123)?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// let json = String::from_utf8(writer)?;
    /// assert_eq!(json, "123");
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not [enabled in the `WriterSettings`](WriterSettings::multi_top_level_value_separator).
    /// Both cases indicate incorrect usage by the user.
    fn number_value<N: FiniteNumber>(&mut self, value: N) -> Result<(), IoError>;

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
    /// # use struson::writer::*;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// json_writer.fp_number_value(4.5)?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// let json = String::from_utf8(writer)?;
    /// assert_eq!(json, "4.5");
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
    /// values are not [enabled in the `WriterSettings`](WriterSettings::multi_top_level_value_separator).
    /// Both cases indicate incorrect usage by the user.
    /*
     * TODO: Maybe give this method a better name?
     * TODO: Maybe also support writing in scientific notation? e.g. `4.1e20`, see also https://doc.rust-lang.org/std/fmt/trait.LowerExp.html
     */
    fn fp_number_value<N: FloatingPointNumber>(&mut self, value: N) -> Result<(), JsonNumberError>;

    /// Serializes a Serde [`Serialize`](serde::ser::Serialize) as next value
    ///
    /// This method is part of the optional Serde integration feature, see the
    /// [`serde` module](crate::serde) of this crate for more information.
    ///
    /// If it is not possible to directly serialize a value in place, instead of using
    /// this method a [`JsonWriterSerializer`](crate::serde::JsonWriterSerializer)
    /// can be constructed and serialization can be performed using it later on. However,
    /// this should only be rarely necessary.
    ///
    /// # Examples
    /// ```
    /// # use struson::writer::*;
    /// # use serde::*;
    /// // In this example JSON bytes are stored in a Vec;
    /// // normally they would be written to a file or network connection
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// // Start writing the enclosing data using the regular JsonWriter methods
    /// json_writer.begin_object()?;
    /// json_writer.name("outer")?;
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
    /// // Serialize the value as next JSON value
    /// json_writer.serialize_value(&value)?;
    ///
    /// // Write the remainder of the enclosing data
    /// json_writer.end_object()?;
    ///
    /// // Ensures that the JSON document is complete and flushes the buffer
    /// json_writer.finish_document()?;
    ///
    /// let json = String::from_utf8(writer)?;
    /// assert_eq!(
    ///     json,
    ///     r#"{"outer":{"text":"some text","number":5}}"#
    /// );
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// Errors can occur when either this JSON writer or the `Serialize` encounters an
    /// error. In which situations this can happen depends on the `Serialize` implementation.
    ///
    /// # Panics
    /// Panics when called on a JSON writer which currently expects a member name, or
    /// when called after the top-level value has already been written and multiple top-level
    /// values are not [enabled in the `WriterSettings`](WriterSettings::multi_top_level_value_separator).
    /// Both cases indicate incorrect usage by the user.
    #[cfg(feature = "serde")]
    fn serialize_value<S: serde::ser::Serialize>(
        &mut self,
        value: &S,
    ) -> Result<(), crate::serde::SerializerError>;

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
    /*
     * Consumes 'self'
     * Note: Dropping writer will not automatically finish document since that would silently discard errors which might occur
     * TODO: Does consuming 'self' here really guarantee that writer cannot be used afterwards anymore; can this be bypassed with reference somehow?
     */
    /*
     * TODO (custom JSON writer support): Instead of returning `()` maybe use an associated type
     * on JsonWriter as result type; then custom JsonWriter implementations which produce a
     * value can return it here.
     */
    fn finish_document(self) -> Result<(), IoError>;
}

/// Writer for lazily writing a JSON string value
///
/// A string value writer can be obtained from [`JsonWriter::string_value_writer`].
///
/// Characters are automatically escaped in the JSON output if necessary. For example
/// the character U+0000 is written as `\u0000`.
///
/// **Important:** Once the string value is finished, [`finish_value`](StringValueWriter::finish_value) must be called.
/// Otherwise the string value writer will still be considered 'active' and all
/// methods of the original JSON writer will panic. Dropping the writer will not
/// automatically finish the value.
///
/// # Errors
/// A [`std::io::Error`] is returned when the underlying writer encounters an error, or
/// when invalid or incomplete UTF-8 data is written.
///
/// # Error behavior
/// The error behavior of this string writer differs from the guarantees made by [`Write`]:
/// - if an error is returned there are no guarantees about if or how many bytes have been written
/// - if an error occurs, processing should be aborted, regardless of the kind of the error;
///   trying to use this string writer or the underlying JSON writer afterwards will lead
///   to unspecified behavior
/* Note: Dropping writer will not automatically finish value since that would silently discard errors which might occur */
pub trait StringValueWriter: Write {
    /// Writes a string value piece
    ///
    /// This method behaves the same way as if all the string bytes were written using
    /// the `write` method, however `JsonWriter` implementations might implement
    /// `write_str` more efficiently. For example, they can omit UTF-8 validation
    /// because the data of a `str` already represents valid UTF-8 data.\
    /// Therefore if a value already exists as string, using `write_str` is likely
    /// at least as efficient as using the `write` method.
    ///
    /// Calls to `write_str` can be mixed with regular `write` calls, however preceding
    /// `write` calls must have written complete UTF-8 data, otherwise an error is returned.
    ///
    /// If an error of kind [`ErrorKind::Interrupted`](std::io::ErrorKind::Interrupted) occurs
    /// while writing, this method will keep retrying to write the data.
    ///
    /// # Examples
    /// ```
    /// # use struson::writer::*;
    /// # use std::io::Write;
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    ///
    /// let mut string_writer = json_writer.string_value_writer()?;
    ///
    /// // Mixes `write_all` and `write_str` calls
    /// string_writer.write_all("one, ".as_bytes())?;
    /// string_writer.write_str("two, ")?;
    /// string_writer.write_all("three ".as_bytes())?;
    /// string_writer.write_str("and four")?;
    /// string_writer.finish_value()?;
    ///
    /// json_writer.finish_document()?;
    ///
    /// let json = String::from_utf8(writer)?;
    /// assert_eq!(json, "\"one, two, three and four\"");
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn write_str(&mut self, s: &str) -> Result<(), IoError> {
        // write_all retries on `ErrorKind::Interrupted`, as desired
        // this is mostly relevant for custom JsonWriter implementations, for JsonStreamWriter it
        // should not matter because it is not expected to return `Interrupted`, see also tests there
        self.write_all(s.as_bytes())
    }

    /// Finishes the JSON string value
    ///
    /// This method must be called when writing the string value is done to allow
    /// using the original JSON writer again.
    ///
    /// # Errors
    /// If the last writing call has started a multi-byte UTF-8 character but has not completed
    /// it, an error is returned.
    /* Consumes 'self' */
    fn finish_value(self) -> Result<(), IoError>;
}

/// Sealed trait for finite number types such as `u32`
///
/// Values of this number type are finite and will therefore always be
/// valid JSON numbers. They will neither be NaN nor Infinity.
///
/// Implementing this trait for custom number types is not possible. Use the
/// method [`JsonWriter::number_value_from_string`] to write them to the JSON
/// document.
pub trait FiniteNumber: private::Sealed {
    /// Converts this number to a JSON number string
    ///
    /// The JSON number string is passed to the given `consumer`.
    fn use_json_number<C: FnOnce(&str) -> Result<(), IoError>>(
        &self,
        consumer: C,
    ) -> Result<(), IoError>;

    /// Gets this number as `u64`
    ///
    /// If this number can be losslessly and relatively efficiently converted
    /// to an `u64`, returns it. Otherwise, or if the number only exists as
    /// string representation, `None` is returned. In that case [`as_i64`](Self::as_i64)
    /// and [`use_json_number`](Self::use_json_number) can be used as fallback.
    /* TODO: Should this use u128 instead? */
    fn as_u64(&self) -> Option<u64>;

    /// Gets this number as `i64`
    ///
    /// If this number can be losslessly and relatively efficiently converted
    /// to an `i64`, returns it. Otherwise, or if the number only exists as
    /// string representation, `None` is returned. In that case [`as_u64`](Self::as_u64)
    /// and [`use_json_number`](Self::use_json_number) can be used as fallback.
    /* TODO: Should this use i128 instead? */
    fn as_i64(&self) -> Option<i64>;
}

/// Sealed trait for floating point number types such as `f64`
///
/// Implementing this trait for custom number types is not possible. Use the
/// method [`JsonWriter::number_value_from_string`] to write them to the JSON
/// document.
pub trait FloatingPointNumber: private::Sealed {
    /// Converts this number to a JSON number string
    ///
    /// The JSON number string is passed to the given `consumer`.
    /// Returns an error if this number is not a valid JSON number, for example
    /// because it is NaN or Infinity.
    fn use_json_number<C: FnOnce(&str) -> Result<(), IoError>>(
        &self,
        consumer: C,
    ) -> Result<(), JsonNumberError>;

    /// Gets this number as `f64`
    ///
    /// If this number can be losslessly and relatively efficiently converted
    /// to a `f64`, returns it. Otherwise, or if the number only exists as
    /// string representation, `None` is returned. In that case
    /// [`use_json_number`](Self::use_json_number) can be used as fallback.
    ///
    /// The `f64` number can be NaN or Infinity, which is not allowed by the
    /// JSON specification. Callers of this method may want to reject these
    /// values when writing them as JSON data.
    fn as_f64(&self) -> Option<f64>;
}

mod private {
    use super::*;

    // Sealed trait, see https://rust-lang.github.io/api-guidelines/future-proofing.html#sealed-traits-protect-against-downstream-implementations-c-sealed
    pub trait Sealed {}

    // Use `duplicate` crate to avoid repeating code for all supported types, see https://stackoverflow.com/a/61467564
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
    IoError(#[from] IoError),
}

// Use `duplicate` crate to avoid repeating code for all supported types, see https://stackoverflow.com/a/61467564
#[duplicate_item(type_template; [u8]; [i8]; [u16]; [i16]; [u32]; [i32]; [u64]; [i64]; [u128]; [i128]; [usize]; [isize])]
impl FiniteNumber for type_template {
    #[inline(always)]
    fn use_json_number<C: FnOnce(&str) -> Result<(), IoError>>(
        &self,
        consumer: C,
    ) -> Result<(), IoError> {
        // TODO: Use https://docs.rs/itoa/latest/itoa/ for better performance? (used also by serde_json)
        let string = self.to_string();
        debug_assert!(
            is_valid_json_number(&string),
            "Unexpected: Not a valid JSON number: {string}"
        );
        consumer(&string)
    }

    fn as_u64(&self) -> Option<u64> {
        // TODO: Should this only use `into()` and for all unsupported types (e.g. signed or u128, ...) always return None?
        #[allow(clippy::useless_conversion, clippy::unnecessary_fallible_conversions /* reason = "for u64 -> u64" */)]
        (*self).try_into().ok()
    }

    fn as_i64(&self) -> Option<i64> {
        // TODO: Should this only use `into()` and for all unsupported types (u64, u128, i128, usize and isize) always return None?
        #[allow(clippy::useless_conversion, clippy::unnecessary_fallible_conversions /* reason = "for i64 -> i64" */)]
        (*self).try_into().ok()
    }
}

#[duplicate_item(type_template; [f32]; [f64])]
impl FloatingPointNumber for type_template {
    #[inline(always)]
    fn use_json_number<C: FnOnce(&str) -> Result<(), IoError>>(
        &self,
        consumer: C,
    ) -> Result<(), JsonNumberError> {
        if self.is_finite() {
            // TODO: Use https://docs.rs/ryu/latest/ryu/ for better performance? (used also by serde_json)
            //   Have to adjust `fp_number_value` documentation then, currently mentions usage of `to_string`
            let string = self.to_string();
            debug_assert!(
                is_valid_json_number(&string),
                "Unexpected: Not a valid JSON number: {string}"
            );
            consumer(&string)?;
            Ok(())
        } else {
            Err(JsonNumberError::InvalidNumber(format!(
                "non-finite number: {self}"
            )))
        }
    }

    fn as_f64(&self) -> Option<f64> {
        #[allow(clippy::useless_conversion)] // for f64 -> f64
        Some((*self).into())
    }
}

/// Number struct which is used by [`JsonReader::transfer_to`] to avoid redundant JSON number string
/// validation by `JsonWriter`
#[derive(Debug)]
pub(crate) struct TransferredNumber<'a>(pub &'a str);
impl private::Sealed for TransferredNumber<'_> {}
impl FiniteNumber for TransferredNumber<'_> {
    fn use_json_number<C: FnOnce(&str) -> Result<(), IoError>>(
        &self,
        consumer: C,
    ) -> Result<(), IoError> {
        consumer(self.0)
    }

    fn as_u64(&self) -> Option<u64> {
        None
    }

    fn as_i64(&self) -> Option<i64> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt::Display;

    #[test]
    fn numbers_strings() {
        fn assert_valid_number<T: FiniteNumber + Display>(number: T) {
            let mut number_string = String::new();
            number
                .use_json_number(|json_number| {
                    number_string.push_str(json_number);
                    Ok(())
                })
                .unwrap();

            assert_eq!(
                true,
                is_valid_json_number(&number_string),
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
            let mut number_string = String::new();
            number
                .use_json_number(|json_number| {
                    number_string.push_str(json_number);
                    Ok(())
                })
                .unwrap();

            assert_eq!(
                true,
                is_valid_json_number(&number_string),
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
            match number.use_json_number(|_| panic!("Should have failed for: {number}")) {
                Ok(_) => panic!("Should have failed for: {number}"),
                Err(e) => match e {
                    JsonNumberError::InvalidNumber(message) => {
                        assert_eq!(format!("non-finite number: {number}"), message)
                    }
                    JsonNumberError::IoError(e) => panic!("Unexpected error for '{number}': {e:?}"),
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
}
