// Implementation based on:
// - https://serde.rs/impl-deserializer.html
// - https://github.com/serde-rs/json/blob/v1.0.107/src/de.rs
//   (trying to match it as close as possible)

use std::{
    fmt::Display,
    num::{ParseFloatError, ParseIntError},
    str::FromStr,
};

use serde::{
    de::{value::StrDeserializer, DeserializeSeed, Error, Unexpected, Visitor},
    forward_to_deserialize_any, Deserialize, Deserializer,
};
use thiserror::Error;

use crate::{
    json_number::is_valid_json_number,
    reader::{JsonReader, ReaderError, ValueType},
};

/// Error which occurred while deserializing a value
/*
 * TODO: For the non-ReaderError variants, should include location?
 *   Would require new methods on JsonReader; one to get peeked location, one to get
 *   location of last value, e.g. when number string was read successfully from JsonReader
 *   but then parsing number fails
 *   Should mention here then how to interpret location information, or refer to `JsonErrorLocation`
 */
#[non_exhaustive]
#[derive(Error, Debug)]
pub enum DeserializerError {
    /// A custom error, normally created by the `DeserializerError::custom` function
    ///
    /// The data of this enum variant is a message describing the error.
    #[error("{0}")]
    Custom(String),
    /// The maximum nesting depth was exceeded while deserializing
    ///
    /// See [`JsonReaderDeserializer::new_with_custom_nesting_limit`] for more information.
    #[error("maximum nesting depth {0} exceeded")]
    MaxNestingDepthExceeded(u32),
    /// The underlying [`JsonReader`] encountered an error
    #[error("{0}")]
    // TODO: Rename to `JsonReaderError`? see `reader::ReaderError` TODO
    ReaderError(#[from] ReaderError),
    /// Parsing a number failed
    ///
    /// The data of this enum variant is a message describing the error.
    #[error("{0}")]
    InvalidNumber(String),
}

impl serde::de::Error for DeserializerError {
    fn custom<T: Display>(msg: T) -> Self {
        DeserializerError::Custom(msg.to_string())
    }
}

impl From<ParseIntError> for DeserializerError {
    fn from(value: ParseIntError) -> Self {
        DeserializerError::InvalidNumber(value.to_string())
    }
}
impl From<ParseFloatError> for DeserializerError {
    fn from(value: ParseFloatError) -> Self {
        DeserializerError::InvalidNumber(value.to_string())
    }
}

// TODO: Should use `serde::de::Error`'s error functions instead of using own error types?

/// Serde `Deserializer` which delegates to a [`JsonReader`]
///
/// Normally there is no need to directly use this deserializer. Instead, the method
/// [`JsonReader::deserialize_next`] can be used.
///
/// # Security
/// In general the security of this deserializer when processing untrusted JSON data highly
/// depends on the implementation of `JsonReader` which is being used. When using
/// [`JsonStreamReader`](crate::reader::JsonStreamReader) see its documentation for more
/// information on its security.
///
/// This deserializer performs UTF-8 validation (implicitly through its usage of `JsonReader`)
/// and implements a [maximum nesting depth](JsonReaderDeserializer::new_with_custom_nesting_limit),
/// but besides that no additional security measures are implemented.
/// In particular it does **not**:
///
/// - Impose a limit on the length of the document
///
///   Especially when the JSON data comes from a compressed data stream (such as gzip) large JSON documents
///   could be used for denial of service attacks.
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
/// - Impose restrictions on number values
///
///   This deserializer parses the JSON numbers provided by the underlying `JsonReader` but does not
///   impose any restrictions on the precision or size of the number values. Care must be taken when
///   using the parsed numbers, especially `i128`, `u128`, `f32` and `f64` values, since they might be
///   extremely large.
///
/// - Impose restrictions on content of member names and string values
///
///   The only restriction is that member names and string values are valid UTF-8 strings, besides
///   that they can contain any code point. They may contain control characters such as the NULL
///   character (`\0`), code points which are not yet assigned a character or invalid graphemes.
///
/// In general is it expected that users of this deserializer, respectively [`Deserialize`] implementations,
/// implement protections against the above mentioned security issues. For example Serde's derived `Deserialize`
/// implementations for structs disallow duplicate fields by default. However, this is not the case for
/// maps ([GitHub issue](https://github.com/serde-rs/serde/issues/1607)).
///
/// # Examples
/// ```
/// # use struson::reader::*;
/// # use struson::serde::*;
/// # use serde::*;
/// // In this example JSON data comes from a string;
/// // normally it would come from a file or a network connection
/// let json = r#"{"text": "some text", "number": 5}"#;
/// let mut json_reader = JsonStreamReader::new(json.as_bytes());
/// let mut deserializer = JsonReaderDeserializer::new(&mut json_reader);
///
/// #[derive(Deserialize, PartialEq, Debug)]
/// struct MyStruct {
///     text: String,
///     number: u64,
/// }
///
/// let value = MyStruct::deserialize(&mut deserializer)?;
///
/// // Ensures that there is no trailing data
/// json_reader.consume_trailing_whitespace()?;
///
/// assert_eq!(
///     MyStruct { text: "some text".to_owned(), number: 5 },
///     value
/// );
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Error handling
/// A [`DeserializerError`] is returned when the underlying `JsonReader`, the
/// deserializer itself or a provided visitor encounters an error.
///
/// When one of the methods of this deserializer return an error, deserialization must be
/// aborted. Trying to call any deserializer methods afterwards can lead to unspecified
/// behavior, such as errors, panics or incorrect data. However, no _undefined_ behavior
/// occurs.
///
/// # Panics
/// Methods of this deserializer and the returned access types (for example `MapAccess`)
/// panic when used in an incorrect way. The documentation of the methods describes in
/// detail the situations when that will happen. In general all these cases are related
/// to incorrect usage by the user (such as trying to deserialize two map keys after each
/// other without a value in between) and are unrelated to the JSON data which is processed.
#[derive(Debug)]
pub struct JsonReaderDeserializer<'a, R: JsonReader> {
    json_reader: &'a mut R,
    // Implement a nesting limit here because due to Deserializer's API cannot deserialize iteratively,
    // so malicious user could provide deeply nested JSON leading to stack overflow
    max_nesting_depth: u32,
    /// Current nesting depth; incremented whenever a JSON array or object is started and
    /// decremented when the array or object is ended
    depth: u32,
}

const DEFAULT_MAX_NESTING_DEPTH: u32 = 128;

impl<'a, R: JsonReader> JsonReaderDeserializer<'a, R> {
    /// Creates a deserializer wrapping a [`JsonReader`]
    ///
    /// The `JsonReader` should be positioned to read the next value, for example it should
    /// not have consumed the top-level value yet or should be inside a JSON array which
    /// has a next item. If this is not the case either an error might be returned during
    /// usage or the deserializer may panic. See the [`JsonReader`] documentation for more
    /// information on when an error or panic can occur.
    ///
    /// The deserializer has a maximum nesting depth of 128, see [`new_with_custom_nesting_limit`](Self::new_with_custom_nesting_limit)
    /// for more information.
    pub fn new(json_reader: &'a mut R) -> Self {
        Self::new_with_custom_nesting_limit(json_reader, DEFAULT_MAX_NESTING_DEPTH)
    }

    /// Creates a deserializer wrapping a [`JsonReader`], with a custom maximum nesting depth
    ///
    /// The `JsonReader` should be positioned to read the next value, for example it should
    /// not have consumed the top-level value yet or should be inside a JSON array which
    /// has a next item. If this is not the case either an error might be returned during
    /// usage or the deserializer may panic. See the [`JsonReader`] documentation for more
    /// information on when an error or panic can occur.
    ///
    /// The maximum nesting depth specifies how many nested JSON arrays or objects this
    /// deserializer is allowed to start before returning [`DeserializerError::MaxNestingDepthExceeded`].
    /// For example a maximum nesting depth of 2 allows the deserializer to start one JSON
    /// array or object and within that another nested array or object, such as `{"outer": {"inner": 1}}`.
    /// Trying to deserialize any further nested JSON array or object will return an error.
    /// The maximum depth does not consider how many JSON arrays or objects the provided
    /// [`JsonReader`] has already started before being using by this deserializer.
    ///
    /// The maximum nesting depth tries to protect against deeply nested JSON data which
    /// could lead to a stack overflow, so high maximum depth values should be used with care.
    /// However, the maximum depth cannot protect against a stack overflow caused by an
    /// error-prone [`Deserialize`] or [`Visitor`] implementation which recursively calls
    /// deserializer methods without actually consuming any value, for example continuously
    /// calling `deserialize_newtype_struct`.
    /* TODO: Better name for this function? */
    pub fn new_with_custom_nesting_limit(json_reader: &'a mut R, max_nesting_depth: u32) -> Self {
        // TODO: Have to ensure that JsonReader currently expects value?
        //   not sure if that is possible without exposing public function for JsonReader
        JsonReaderDeserializer {
            json_reader,
            max_nesting_depth,
            depth: 0,
        }
    }
}

fn map_to_unexpected<'a>(peeked: ValueType) -> Unexpected<'a> {
    match peeked {
        ValueType::Array => Unexpected::Seq,
        ValueType::Object => Unexpected::Map,
        ValueType::Null => Unexpected::Unit,
        // For these fail fast without complete value being available
        ValueType::String => Unexpected::Other("string"),
        ValueType::Number => Unexpected::Other("number"),
        ValueType::Boolean => Unexpected::Other("bool"),
    }
}

fn err_unexpected_type<'de, V: Visitor<'de>>(
    peeked: ValueType,
    visitor: &V,
) -> Result<V::Value, DeserializerError> {
    Err(DeserializerError::invalid_type(
        map_to_unexpected(peeked),
        visitor,
    ))
}

macro_rules! check_nesting {
    ($self:ident, $body:block) => {
        if $self.depth >= $self.max_nesting_depth {
            Err(DeserializerError::MaxNestingDepthExceeded(
                $self.max_nesting_depth,
            ))
        } else {
            $self.depth += 1;
            let result = $body;
            $self.depth -= 1;
            result
        }
    };
}

impl<R: JsonReader> JsonReaderDeserializer<'_, R> {
    fn deserialize_seq_with_length<'de, V: Visitor<'de>>(
        &mut self,
        visitor: V,
        expected_len: Option<usize>,
    ) -> Result<V::Value, DeserializerError> {
        return check_nesting!(self, {
            self.json_reader.begin_array()?;
            let mut seq = SeqAccess {
                de: self,
                expected_len,
                len: 0,
            };
            // Use `?` here to already fail fast before calling end_array()
            let result = visitor.visit_seq(&mut seq)?;
            if let Some(expected_len) = expected_len {
                if seq.len < expected_len {
                    return Err(DeserializerError::invalid_length(
                        seq.len,
                        &format!("array of length {expected_len}").as_str(),
                    ));
                }
            }

            self.json_reader.end_array()?;
            Ok(result)
        });
    }
}

/* TODO: Move this documentation to the struct documentation? */
/// This implementation of [`Deserializer`] tries to match Serde JSON's behavior, however there
/// might be some minor differences. Where relevant the documentation of the methods describes
/// how exactly a value is deserialized from JSON. Borrowing strings or bytes with the lifetime
/// of this deserializer (`'de`) is not supported.
///
/// If the exact behavior of Serde JSON is needed, the following workaround can be used, at the
/// cost of potentially worse performance:
/// ```
/// # use struson::reader::*;
/// # use struson::writer::*;
/// # use serde::Deserialize;
/// #
/// # let mut json_reader = JsonStreamReader::new(r#"{"text": "some text", "number": 5}"#.as_bytes());
/// // Let's assume you already have a JsonReader called `json_reader`
///
/// #[derive(Deserialize, PartialEq, Debug)]
/// struct MyStruct {
///     text: String,
///     number: u64,
/// }
///
/// // 1. Create a temporary JsonStreamWriter which writes to a Vec
/// let mut writer = Vec::<u8>::new();
/// let mut json_writer = JsonStreamWriter::new(&mut writer);
///
/// // 2. Transfer the JSON data of the next value to the `json_writer`, and flush the writer
/// json_reader.transfer_to(&mut json_writer)?;
/// json_writer.finish_document()?;
///
/// // 3. Deserialize the value from string with Serde JSON
/// let json = String::from_utf8(writer)?;
/// let value: MyStruct = serde_json::from_str(&json)?;
///
/// // Continue using `json_reader` ...
/// # assert_eq!(
/// #     MyStruct { text: "some text".to_string(), number: 5 },
/// #     value
/// # );
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
/*
 * JsonReader does not support borrowing data, so 'de is not bound to it
 * TODO: In the documentation of the methods below use links when referring to other method,
 *   e.g. [`deserialize_map`]; however, rustdoc seems to be unable to create links?
 */
impl<'de, R: JsonReader> Deserializer<'de> for &mut JsonReaderDeserializer<'_, R> {
    type Error = DeserializerError;

    /// Require the `Deserializer` to figure out how to drive the visitor based
    /// on what data type is in the input
    ///
    /// The behavior depends on the type of the next JSON value:
    /// - JSON array: delegates to `deserialize_seq`
    /// - JSON object: delegates to `deserialize_map`
    /// - JSON string: delegates to `deserialize_string`
    /// - JSON boolean: delegates to `deserialize_bool`
    /// - JSON `null`: consumes the `null` and calls [`Visitor::visit_unit`]
    /// - JSON number:
    ///   - if number contains `.`, `e` or `E`: parses it as `f64` and calls [`Visitor::visit_f64`]
    ///   - otherwise, if number starts with `-`: parses it as `i64` and calls [`Visitor::visit_i64`];
    ///     if parsing fails falls back to parsing as `i128`
    ///   - otherwise: parses it as `u64` and calls [`Visitor::visit_u64`]; if parsing fails falls
    ///     back to parsing as `u128`
    ///
    ///   An error is returned if parsing the number fails.
    fn deserialize_any<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        match self.json_reader.peek()? {
            ValueType::Array => self.deserialize_seq(visitor),
            ValueType::Object => self.deserialize_map(visitor),
            // Deserialize as `String` instead of `str`, assuming that user might want to consume the value
            ValueType::String => self.deserialize_string(visitor),
            ValueType::Boolean => self.deserialize_bool(visitor),
            ValueType::Null => {
                self.json_reader.next_null()?;
                visitor.visit_unit()
            }
            ValueType::Number => {
                // Note: This does not completely match serde_json's behavior, but maybe this implementation here is more reasonable?
                let number_str = self.json_reader.next_number_as_str()?;
                if number_str.contains(['.', 'e', 'E']) {
                    visitor.visit_f64(f64::from_str(number_str)?)
                } else if number_str.as_bytes()[0] == b'-' {
                    match i64::from_str(number_str) {
                        Ok(number) => visitor.visit_i64(number),
                        // Fall back to i128
                        Err(_) => visitor.visit_i128(i128::from_str(number_str)?),
                    }
                } else {
                    match u64::from_str(number_str) {
                        Ok(number) => visitor.visit_u64(number),
                        // Fall back to u128
                        Err(_) => visitor.visit_u128(u128::from_str(number_str)?),
                    }
                }
            }
        }
    }

    fn deserialize_bool<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_bool(self.json_reader.next_bool()?)
    }

    // Note: The following number deserialization methods don't match serde_json;
    // serde_json deserializes only as u64, i64 and f64 depending on the format of
    // the number, ignoring the originally requested type

    // TODO: Are these implementations too strict when requesting integer number
    // but JSON number is floating point? Should they fall back to `visit_f64` then?

    fn deserialize_i8<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_i8(self.json_reader.next_number()??)
    }

    fn deserialize_i16<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_i16(self.json_reader.next_number()??)
    }

    fn deserialize_i32<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_i32(self.json_reader.next_number()??)
    }

    fn deserialize_i64<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_i64(self.json_reader.next_number()??)
    }

    fn deserialize_i128<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_i128(self.json_reader.next_number()??)
    }

    fn deserialize_u8<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_u8(self.json_reader.next_number()??)
    }

    fn deserialize_u16<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_u16(self.json_reader.next_number()??)
    }

    fn deserialize_u32<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_u32(self.json_reader.next_number()??)
    }

    fn deserialize_u64<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_u64(self.json_reader.next_number()??)
    }

    fn deserialize_u128<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_u128(self.json_reader.next_number()??)
    }

    fn deserialize_f32<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_f32(self.json_reader.next_number()??)
    }

    fn deserialize_f64<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_f64(self.json_reader.next_number()??)
    }

    /// Hint that the `Deserialize` type is expecting a `char` value
    ///
    /// This implementation delegates to `deserialize_str`.
    fn deserialize_char<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.deserialize_str(visitor)
    }

    /// Hint that the `Deserialize` type is expecting a string value
    ///
    /// This implementation expects that the next value is a JSON string value
    /// and calls [`Visitor::visit_str`] with the value. For all other JSON
    /// values an error is returned. Borrowing a string with the lifetime of
    /// this deserializer (`'de`) is not supported.
    fn deserialize_str<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_str(self.json_reader.next_str()?)
    }

    fn deserialize_string<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        // This differs from serde_json's behavior (https://github.com/serde-rs/json/blob/v1.0.107/src/de.rs#L1548),
        // which delegates to `deserialize_str`
        // However, if caller explicitly requests a String, then it might be better to always
        // provide them a String (because the current `deserialize_str` implementation here would
        // not do that)
        visitor.visit_string(self.json_reader.next_string()?)
    }

    /// Hint that the `Deserialize` type is expecting a byte array
    ///
    /// The behavior depends on the type of the next JSON value:
    /// - JSON string: [`Visitor::visit_bytes`] is called with the UTF-8 bytes of the string value
    /// - JSON array: delegates to `deserialize_seq`; the type of the array
    ///   items is not checked, for example the array could contain boolean values, numbers,
    ///   strings or even nested arrays
    ///
    /// For all other JSON values an error is returned. Borrowing bytes with the lifetime of
    /// this deserializer (`'de`) is not supported.
    ///
    /// Unlike Serde JSON's implementation of this method, this implementation requires that the
    /// JSON string value consists of valid UTF-8 bytes. It is not possible to read invalid UTF-8
    /// strings with this method.
    fn deserialize_bytes<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        // Is equivalent to serde_json's behavior (https://github.com/serde-rs/json/blob/v1.0.107/src/de.rs#L1621)
        match self.json_reader.peek()? {
            ValueType::String => visitor.visit_bytes(self.json_reader.next_str()?.as_bytes()),
            // Note: This matches serde_json's behavior, but does not actually call `visit_bytes`,
            // nor does it enforce that values are all u8
            ValueType::Array => self.deserialize_seq(visitor),
            peeked => err_unexpected_type(peeked, &visitor),
        }
    }

    /// Hint that the `Deserialize` type is expecting a byte array
    ///
    /// The behavior depends on the type of the next JSON value:
    /// - JSON string: [`Visitor::visit_byte_buf`] is called with the UTF-8 bytes of the string value
    /// - JSON array: delegates to `deserialize_seq`; the type of the array
    ///   items is not checked, for example the array could contain boolean values, numbers,
    ///   strings or even nested arrays
    ///
    /// For all other JSON values an error is returned.
    ///
    /// Unlike Serde JSON's implementation of this method, this implementation requires that the
    /// JSON string value consists of valid UTF-8 bytes. It is not possible to read invalid UTF-8
    /// strings with this method.
    fn deserialize_byte_buf<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        // This differs from serde_json's behavior (https://github.com/serde-rs/json/blob/v1.0.107/src/de.rs#L1656),
        // which delegates to `deserialize_bytes`
        // However, if caller explicitly requests a byte buf, then it might be better to always
        // provide them a byte buf (because the current `deserialize_bytes` implementation here would
        // not do that)
        match self.json_reader.peek()? {
            ValueType::String => {
                visitor.visit_byte_buf(self.json_reader.next_string()?.into_bytes())
            }
            // Note: This matches serde_json's behavior, but does not actually call `visit_bytes` / `visit_byte_buf`,
            // nor does it enforce that values are all u8
            ValueType::Array => self.deserialize_seq(visitor),
            peeked => err_unexpected_type(peeked, &visitor),
        }
    }

    /// Hint that the `Deserialize` type is expecting an optional value
    ///
    /// If the next value is a JSON `null`, consumes it and calls [`Visitor::visit_none`].
    /// Otherwise calls [`Visitor::visit_some`] to let it read the value.
    fn deserialize_option<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        match self.json_reader.peek()? {
            ValueType::Null => {
                self.json_reader.next_null()?;
                visitor.visit_none()
            }
            _ => visitor.visit_some(self),
        }
    }

    /// Hint that the `Deserialize` type is expecting a unit value
    ///
    /// If the next value is a JSON `null`, consumes it and calls [`Visitor::visit_unit`].
    /// Otherwise returns an error due to the unexpected value type.
    fn deserialize_unit<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.json_reader.next_null()?;
        visitor.visit_unit()
    }

    /// Hint that the `Deserialize` type is expecting a unit struct
    ///
    /// This implementation delegates to `deserialize_unit`,
    /// the given name is ignored.
    fn deserialize_unit_struct<V: Visitor<'de>>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        self.deserialize_unit(visitor)
    }

    /// Hint that the `Deserialize` type is expecting a newtype struct
    ///
    /// This implementation simply calls [`Visitor::visit_newtype_struct`], the
    /// given name is ignored.
    fn deserialize_newtype_struct<V: Visitor<'de>>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        visitor.visit_newtype_struct(self)
    }

    /// Hint that the `Deserialize` type is expecting a sequence of values
    ///
    /// If the next value is a JSON array, starts the array, calls [`Visitor::visit_seq`]
    /// and afterwards ends the array. Otherwise, if the value is not a JSON array, an
    /// error is returned.
    fn deserialize_seq<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.deserialize_seq_with_length(visitor, None)
    }

    /// Hint that the `Deserialize` type is expecting a sequence of values
    ///
    /// This implementation delegates to `deserialize_seq` and
    /// verifies that exactly `len` elements are read, returning an error otherwise.
    fn deserialize_tuple<V: Visitor<'de>>(
        self,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        self.deserialize_seq_with_length(visitor, Some(len))
    }

    /// Hint that the `Deserialize` type is expecting a tuple struct
    ///
    /// This implementation delegates to `deserialize_seq` and
    /// verifies that exactly `len` elements are read, returning an error otherwise.
    /// The given name is ignored.
    fn deserialize_tuple_struct<V: Visitor<'de>>(
        self,
        _name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        self.deserialize_seq_with_length(visitor, Some(len))
    }

    /// Hint that the `Deserialize` type is expecting a map of key-value pairs
    ///
    /// If the next value is a JSON object, starts the object, calls [`Visitor::visit_map`]
    /// and afterwards ends the object. Otherwise, if the value is not a JSON object, an
    /// error is returned.
    ///
    /// Duplicate keys are not detected or prevented.
    ///
    /// # Panics
    /// For every call to [`MapAccess::next_key`](serde::de::MapAccess::next_key) which returns
    /// `Some` a call to [`MapAccess::next_value`](serde::de::MapAccess::next_value)
    /// has to be made. Calling the methods in a different order or trying to consume
    /// a different number of keys than values will cause a panic.
    fn deserialize_map<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        return check_nesting!(self, {
            self.json_reader.begin_object()?;
            let mut map_access = MapAccess {
                de: self,
                // Initially entry key is expected
                expects_entry_value: false,
            };
            // Use `?` here to already fail fast before calling end_object()
            let result = visitor.visit_map(&mut map_access)?;
            // Check this explicitly in case custom JsonReader implementation does not detect this
            if map_access.expects_entry_value {
                panic!("Incorrect usage: Did not deserialize trailing value");
            }

            self.json_reader.end_object()?;
            Ok(result)
        });
    }

    /// Hint that the `Deserialize` type is expecting a struct
    ///
    /// The behavior depends on the type of the next JSON value:
    /// - JSON array: delegates to `deserialize_seq`
    /// - JSON object: delegates to `deserialize_map`
    ///
    /// For all other JSON values an error is returned. The given name and
    /// fields are ignored.
    fn deserialize_struct<V: Visitor<'de>>(
        self,
        _name: &'static str,
        // TODO: Should fields be checked in deserialized value? Though serde_json does not seem to do that either
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        match self.json_reader.peek()? {
            ValueType::Array => self.deserialize_seq(visitor),
            ValueType::Object => self.deserialize_map(visitor),
            peeked => return err_unexpected_type(peeked, &visitor),
        }
    }

    /// Hint that the `Deserialize` type is expecting an enum value
    ///
    /// The behavior depends on the type of the next JSON value:
    /// - JSON object: an object with one member is expected, where the member name is
    ///   the enum variant name and the member value is the variant value
    /// - JSON string: the string is the variant name; the value is expected to be unit
    ///   and has to be consumed with [`VariantAccess::unit_variant`](serde::de::VariantAccess::unit_variant),
    ///   using any other method will return an error
    ///
    /// In both cases [`Visitor::visit_enum`] is called. For all other JSON values an
    /// error is returned. The given name and fields are ignored.
    ///
    /// # Panics
    /// The variant name must be read from the `EnumAccess` passed to `visit_enum` and
    /// afterwards the corresponding value has to be read from the `VariantAccess`.
    /// This method panics if the visitor returns `Ok` without having read the variant
    /// name or variant value.
    fn deserialize_enum<V: Visitor<'de>>(
        self,
        _name: &'static str,
        // TODO: Should variants be validated? Though serde_json does not seem to do that either
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        match self.json_reader.peek()? {
            ValueType::Object => {
                return check_nesting!(self, {
                    self.json_reader.begin_object()?;
                    let mut variant_access = VariantAccess {
                        de: self,
                        // Initially value has not been consumed
                        consumed_variant_value: false,
                    };
                    // Use `?` here to already fail fast before calling end_object()
                    let result = visitor.visit_enum(&mut variant_access)?;

                    if !variant_access.consumed_variant_value {
                        panic!("Incorrect usage: Did not consume variant value");
                    }

                    self.json_reader.end_object()?;
                    Ok(result)
                });
            }
            ValueType::String => {
                let mut variant_access = UnitVariantAccess {
                    de: self,
                    // Initially value has not been consumed
                    consumed_variant_value: false,
                };
                // Use `?` here to already fail fast before checking if value was consumed
                let result = visitor.visit_enum(&mut variant_access)?;
                if !variant_access.consumed_variant_value {
                    panic!("Incorrect usage: Did not consume variant value");
                }
                Ok(result)
            }
            peeked => return err_unexpected_type(peeked, &visitor),
        }
    }

    /// Hint that the `Deserialize` type is expecting an identifier
    ///
    /// This implementation delegates to `deserialize_str`.
    fn deserialize_identifier<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.deserialize_str(visitor)
    }

    /// Hint that the `Deserialize` type needs to ignore the next value
    ///
    /// The next value, regardless of its type, is ignored and [`Visitor::visit_unit`]
    /// is called.
    fn deserialize_ignored_any<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.json_reader.skip_value()?;
        visitor.visit_unit()
    }
}

#[derive(Debug)]
struct SeqAccess<'s, 'a, R: JsonReader> {
    de: &'s mut JsonReaderDeserializer<'a, R>,
    expected_len: Option<usize>,
    len: usize,
}
impl<'de, R: JsonReader> serde::de::SeqAccess<'de> for &mut SeqAccess<'_, '_, R> {
    type Error = DeserializerError;

    fn next_element_seed<T: DeserializeSeed<'de>>(
        &mut self,
        seed: T,
    ) -> Result<Option<T::Value>, Self::Error> {
        if self.de.json_reader.has_next()? {
            // Only check this if there is really a next element; maybe caller just wanted to assert that next
            // `next_element_seed` call returns None
            if let Some(expected_len) = self.expected_len {
                if self.len >= expected_len {
                    return Err(DeserializerError::invalid_length(
                        // + 1 for currently read element
                        self.len + 1,
                        &format!("array of length {expected_len}").as_str(),
                    ));
                }
                self.len += 1;
            }

            Ok(Some(seed.deserialize(&mut *self.de)?))
        } else {
            Ok(None)
        }
    }
}

#[derive(Debug)]
struct MapAccess<'s, 'a, R: JsonReader> {
    de: &'s mut JsonReaderDeserializer<'a, R>,
    expects_entry_value: bool,
}
impl<'de, R: JsonReader> serde::de::MapAccess<'de> for &mut MapAccess<'_, '_, R> {
    type Error = DeserializerError;

    fn next_key_seed<K: DeserializeSeed<'de>>(
        &mut self,
        seed: K,
    ) -> Result<Option<K::Value>, Self::Error> {
        if self.expects_entry_value {
            panic!("Incorrect usage: Cannot deserialize key when value is expected")
        }
        if self.de.json_reader.has_next()? {
            let key = seed.deserialize(MapKeyDeserializer {
                // Uses borrowed `str` instead of `String` assuming that is the more common use case
                key: self.de.json_reader.next_name()?,
            })?;
            self.expects_entry_value = true;
            Ok(Some(key))
        } else {
            Ok(None)
        }
    }

    fn next_value_seed<V: DeserializeSeed<'de>>(
        &mut self,
        seed: V,
    ) -> Result<V::Value, Self::Error> {
        if !self.expects_entry_value {
            panic!("Incorrect usage: Cannot deserialize value when key is expected")
        }
        self.expects_entry_value = false;
        seed.deserialize(&mut *self.de)
    }
}

#[derive(Debug)]
struct MapKeyDeserializer<'a> {
    key: &'a str,
}

// Roughly based on https://github.com/serde-rs/json/blob/v1.0.107/src/de.rs#L2130
macro_rules! deserialize_number_key {
    ($deserialize:ident => $visit:ident) => {
        fn $deserialize<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
            if is_valid_json_number(self.key) {
                // serde_json calls method on underlying Deserializer; not possible here because only the
                // key as str is available here
                if let Ok(number) = self.key.parse() {
                    visitor.$visit(number)
                } else {
                    Err(DeserializerError::InvalidNumber(format!(
                        "number {} cannot be parsed as desired type",
                        self.key
                    )))
                }
            } else {
                Err(DeserializerError::InvalidNumber(format!(
                    "invalid number: {}",
                    self.key
                )))
            }
        }
    };
}

// Based on https://github.com/serde-rs/json/blob/v1.0.107/src/de.rs#L2171
impl<'de> Deserializer<'de> for MapKeyDeserializer<'_> {
    type Error = DeserializerError;

    fn deserialize_any<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_str(self.key)
    }

    // This does not match serde_json's behavior, expect for i128 and u128 (and f32 with `float_roundtrip` feature)
    // serde_json deserializes based on the JSON number format and ignores which `deserialize_...` method was called
    deserialize_number_key!(deserialize_i8 => visit_i8);
    deserialize_number_key!(deserialize_i16 => visit_i16);
    deserialize_number_key!(deserialize_i32 => visit_i32);
    deserialize_number_key!(deserialize_i64 => visit_i64);
    deserialize_number_key!(deserialize_i128 => visit_i128);

    deserialize_number_key!(deserialize_u8 => visit_u8);
    deserialize_number_key!(deserialize_u16 => visit_u16);
    deserialize_number_key!(deserialize_u32 => visit_u32);
    deserialize_number_key!(deserialize_u64 => visit_u64);
    deserialize_number_key!(deserialize_u128 => visit_u128);

    deserialize_number_key!(deserialize_f32 => visit_f32);
    deserialize_number_key!(deserialize_f64 => visit_f64);

    fn deserialize_option<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        visitor.visit_some(self)
    }

    fn deserialize_newtype_struct<V: Visitor<'de>>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_enum<V: Visitor<'de>>(
        self,
        name: &'static str,
        variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        // Note: This might deviate from serde_json, but only map key as String is available here
        // so cannot delegate to the original Deserializer; ideally would use UnitVariantAccess here
        // but that is also not possible because it requires Deserializer as well
        StrDeserializer::new(self.key).deserialize_enum(name, variants, visitor)
    }

    fn deserialize_bytes<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        // This matches JsonReaderDeserializer.deserialize_bytes
        visitor.visit_bytes(self.key.as_bytes())
    }

    fn deserialize_byte_buf<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        self.deserialize_bytes(visitor)
    }

    fn deserialize_bool<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, Self::Error> {
        match self.key {
            "true" => visitor.visit_bool(true),
            "false" => visitor.visit_bool(false),
            _ => Err(DeserializerError::invalid_type(
                Unexpected::Str(self.key),
                &visitor,
            )),
        }
    }

    // TODO: Should this really contain `ignored_any` as well? serde_json behaves the same
    // way but it is not consistent with JsonReaderDeserializer which calls `visit_unit`
    forward_to_deserialize_any! {
        char str string unit unit_struct seq tuple tuple_struct map
        struct identifier ignored_any
    }
}

/// `EnumAccess` and `VariantAccess` for enums encoded as JSON object: `{"variant_name": variant_value}`
#[derive(Debug)]
struct VariantAccess<'s, 'a, R: JsonReader> {
    de: &'s mut JsonReaderDeserializer<'a, R>,
    // Used to verify that user consumed variant value; otherwise they might return without consuming
    // variant value which would leave Deserializer in inconsistent state
    consumed_variant_value: bool,
}

impl<'de, R: JsonReader> serde::de::EnumAccess<'de> for &mut VariantAccess<'_, '_, R> {
    type Error = DeserializerError;
    type Variant = Self;

    fn variant_seed<V: DeserializeSeed<'de>>(
        self,
        seed: V,
    ) -> Result<(V::Value, Self::Variant), Self::Error> {
        // Uses borrowed `str` instead of `String` assuming that is the more common use case
        let name = self.de.json_reader.next_name()?;
        // TODO: This does not completely match serde_json behavior, but cannot pass `self.de` because JsonReader does not
        // allow reading name as regular string value; serde_json's behavior seems to be slightly incorrect though, see
        // https://github.com/serde-rs/json/issues/979
        let de = StrDeserializer::<Self::Error>::new(name);
        Ok((seed.deserialize(de)?, self))
    }
}

impl<'de, R: JsonReader> serde::de::VariantAccess<'de> for &mut VariantAccess<'_, '_, R> {
    type Error = DeserializerError;

    fn unit_variant(self) -> Result<(), Self::Error> {
        self.consumed_variant_value = true;
        // Deserialize `()`
        Deserialize::deserialize(&mut *self.de)
    }

    fn newtype_variant_seed<T: DeserializeSeed<'de>>(
        self,
        seed: T,
    ) -> Result<T::Value, Self::Error> {
        self.consumed_variant_value = true;
        seed.deserialize(&mut *self.de)
    }

    fn tuple_variant<V: Visitor<'de>>(
        self,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        self.consumed_variant_value = true;
        // Note: serde_json calls `deserialize_seq`, however here the current implementation
        // of `deserialize_tuple` eventually calls `deserialize_seq` as well
        self.de.deserialize_tuple(len, visitor)
    }

    fn struct_variant<V: Visitor<'de>>(
        self,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        self.consumed_variant_value = true;
        self.de.deserialize_struct("", fields, visitor)
    }
}

/// `EnumAccess` and `VariantAccess` for enums whose variant name is encoded as JSON string value
/// without a variant value (implicit unit value)
#[derive(Debug)]
struct UnitVariantAccess<'s, 'a, R: JsonReader> {
    de: &'s mut JsonReaderDeserializer<'a, R>,
    // Used to verify that user consumed variant value; otherwise they might return without consuming
    // variant value which would leave Deserializer in inconsistent state
    consumed_variant_value: bool,
}

impl<'de, R: JsonReader> serde::de::EnumAccess<'de> for &mut UnitVariantAccess<'_, '_, R> {
    type Error = DeserializerError;
    type Variant = Self;

    fn variant_seed<V: DeserializeSeed<'de>>(
        self,
        seed: V,
    ) -> Result<(V::Value, Self::Variant), Self::Error> {
        // Deserialize the string value (only for string value UnitVariantAccess is created)
        Ok((seed.deserialize(&mut *self.de)?, self))
    }
}

impl<'de, R: JsonReader> serde::de::VariantAccess<'de> for &mut UnitVariantAccess<'_, '_, R> {
    type Error = DeserializerError;

    fn unit_variant(self) -> Result<(), Self::Error> {
        self.consumed_variant_value = true;
        Ok(())
    }

    fn newtype_variant_seed<T: DeserializeSeed<'de>>(
        self,
        _seed: T,
    ) -> Result<T::Value, Self::Error> {
        Err(DeserializerError::invalid_type(
            Unexpected::UnitVariant,
            &"newtype variant",
        ))
    }

    fn tuple_variant<V: Visitor<'de>>(
        self,
        _len: usize,
        _visitor: V,
    ) -> Result<V::Value, Self::Error> {
        Err(DeserializerError::invalid_type(
            Unexpected::UnitVariant,
            &"tuple variant",
        ))
    }

    fn struct_variant<V: Visitor<'de>>(
        self,
        _fields: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value, Self::Error> {
        Err(DeserializerError::invalid_type(
            Unexpected::UnitVariant,
            &"struct variant",
        ))
    }
}

#[cfg(test)]
mod tests {
    use std::io::ErrorKind;

    use serde::de::VariantAccess;
    use serde_json::de::StrRead;

    use super::*;
    use crate::reader::{
        JsonErrorLocation, JsonStreamReader, ReaderSettings, SyntaxErrorKind,
        UnexpectedStructureKind,
    };

    #[derive(PartialEq, Clone, Debug)]
    enum Visited {
        Bool(bool),
        I8(i8),
        I16(i16),
        I32(i32),
        I64(i64),
        I128(i128),
        U8(u8),
        U16(u16),
        U32(u32),
        U64(u64),
        U128(u128),
        F32(f32),
        F64(f64),
        Char(char),
        Str(String),
        BorrowedStr(String),
        String(String),
        Bytes(Vec<u8>),
        BorrowedBytes(Vec<u8>),
        ByteBuf(Vec<u8>),
        None,
        Unit,
        SomeStart,
        SomeEnd,
        NewtypeStructStart,
        NewtypeStructEnd,
        SeqStart,
        SeqEnd,
        MapStart,
        MapEnd,
        EnumStart,
        EnumEnd,
    }

    enum EnumVariantHandling {
        Unit,
        Newtype,
        Tuple(usize),
        Struct(&'static [&'static str]),
    }

    // TODO: Suggest to serde_test maintainer to add something similar to this to allow testing custom Deserializer?
    struct TrackingVisitor {
        visited: Vec<Visited>,
        enum_variant_handling: EnumVariantHandling,
    }
    impl TrackingVisitor {
        fn new(enum_variant_handling: EnumVariantHandling) -> Self {
            TrackingVisitor {
                visited: Vec::new(),
                enum_variant_handling,
            }
        }

        fn visit<E>(&mut self, visited: Visited) -> Result<(), E> {
            self.visited.push(visited);
            Ok(())
        }
    }
    impl<'de> Visitor<'de> for &mut TrackingVisitor {
        type Value = ();

        fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(formatter, "custom-test-value")
        }

        fn visit_bool<E>(self, v: bool) -> Result<Self::Value, E> {
            self.visit(Visited::Bool(v))
        }

        fn visit_i8<E>(self, v: i8) -> Result<Self::Value, E> {
            self.visit(Visited::I8(v))
        }

        fn visit_i16<E>(self, v: i16) -> Result<Self::Value, E> {
            self.visit(Visited::I16(v))
        }

        fn visit_i32<E>(self, v: i32) -> Result<Self::Value, E> {
            self.visit(Visited::I32(v))
        }

        fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E> {
            self.visit(Visited::I64(v))
        }

        fn visit_i128<E>(self, v: i128) -> Result<Self::Value, E> {
            self.visit(Visited::I128(v))
        }

        fn visit_u8<E>(self, v: u8) -> Result<Self::Value, E> {
            self.visit(Visited::U8(v))
        }

        fn visit_u16<E>(self, v: u16) -> Result<Self::Value, E> {
            self.visit(Visited::U16(v))
        }

        fn visit_u32<E>(self, v: u32) -> Result<Self::Value, E> {
            self.visit(Visited::U32(v))
        }

        fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E> {
            self.visit(Visited::U64(v))
        }

        fn visit_u128<E>(self, v: u128) -> Result<Self::Value, E> {
            self.visit(Visited::U128(v))
        }

        fn visit_f32<E>(self, v: f32) -> Result<Self::Value, E> {
            self.visit(Visited::F32(v))
        }

        fn visit_f64<E>(self, v: f64) -> Result<Self::Value, E> {
            self.visit(Visited::F64(v))
        }

        fn visit_char<E>(self, v: char) -> Result<Self::Value, E> {
            self.visit(Visited::Char(v))
        }

        fn visit_str<E>(self, v: &str) -> Result<Self::Value, E> {
            self.visit(Visited::Str(v.to_owned()))
        }

        fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E> {
            self.visit(Visited::BorrowedStr(v.to_owned()))
        }

        fn visit_string<E>(self, v: String) -> Result<Self::Value, E> {
            self.visit(Visited::String(v))
        }

        fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E> {
            self.visit(Visited::Bytes(v.to_owned()))
        }

        fn visit_borrowed_bytes<E>(self, v: &'de [u8]) -> Result<Self::Value, E> {
            self.visit(Visited::BorrowedBytes(v.to_owned()))
        }

        fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E> {
            self.visit(Visited::ByteBuf(v))
        }

        fn visit_none<E>(self) -> Result<Self::Value, E> {
            self.visit(Visited::None)
        }

        fn visit_some<D: Deserializer<'de>>(
            self,
            deserializer: D,
        ) -> Result<Self::Value, D::Error> {
            self.visit(Visited::SomeStart)?;
            deserializer.deserialize_any(&mut *self)?;
            self.visit(Visited::SomeEnd)
        }

        fn visit_unit<E>(self) -> Result<Self::Value, E> {
            self.visit(Visited::Unit)
        }

        fn visit_newtype_struct<D: Deserializer<'de>>(
            self,
            deserializer: D,
        ) -> Result<Self::Value, D::Error> {
            self.visit(Visited::NewtypeStructStart)?;
            deserializer.deserialize_any(&mut *self)?;
            self.visit(Visited::NewtypeStructEnd)
        }

        fn visit_seq<A: serde::de::SeqAccess<'de>>(
            self,
            mut seq: A,
        ) -> Result<Self::Value, A::Error> {
            self.visit(Visited::SeqStart)?;

            while seq
                .next_element_seed(VisitingDeserialize { visitor: self })?
                .is_some()
            {}

            self.visit(Visited::SeqEnd)
        }

        fn visit_map<A: serde::de::MapAccess<'de>>(
            self,
            mut map: A,
        ) -> Result<Self::Value, A::Error> {
            self.visit(Visited::MapStart)?;

            while map
                .next_key_seed(VisitingDeserialize { visitor: self })?
                .is_some()
            {
                map.next_value_seed(VisitingDeserialize { visitor: self })?;
            }

            self.visit(Visited::MapEnd)
        }

        fn visit_enum<A: serde::de::EnumAccess<'de>>(
            self,
            data: A,
        ) -> Result<Self::Value, A::Error> {
            self.visit(Visited::EnumStart)?;

            let (_, variant) = data.variant_seed(VisitingDeserialize { visitor: self })?;
            match self.enum_variant_handling {
                EnumVariantHandling::Unit => variant.unit_variant()?,
                EnumVariantHandling::Newtype => {
                    variant.newtype_variant_seed(VisitingDeserialize { visitor: self })?
                }
                EnumVariantHandling::Tuple(len) => variant.tuple_variant(len, &mut *self)?,
                EnumVariantHandling::Struct(fields) => {
                    variant.struct_variant(fields, &mut *self)?
                }
            }

            self.visit(Visited::EnumEnd)
        }
    }

    struct VisitingDeserialize<'a> {
        visitor: &'a mut TrackingVisitor,
    }
    impl<'de> DeserializeSeed<'de> for VisitingDeserialize<'_> {
        type Value = ();

        fn deserialize<D: Deserializer<'de>>(
            self,
            deserializer: D,
        ) -> Result<Self::Value, D::Error> {
            deserializer.deserialize_any(self.visitor)
        }
    }

    fn assert_deserialized_enum<
        F: Fn(
            &mut JsonReaderDeserializer<'_, JsonStreamReader<&[u8]>>,
            &mut TrackingVisitor,
        ) -> Result<(), DeserializerError>,
    >(
        json: &str,
        enum_variant_handling: EnumVariantHandling,
        deserializing_function: F,
        expected_visited: &[Visited],
    ) {
        let mut json_reader = JsonStreamReader::new(json.as_bytes());
        let mut deserializer = JsonReaderDeserializer::new(&mut json_reader);
        let mut visitor = TrackingVisitor::new(enum_variant_handling);
        deserializing_function(&mut deserializer, &mut visitor).unwrap();
        json_reader.consume_trailing_whitespace().unwrap();

        assert_eq!(
            expected_visited, visitor.visited,
            "expected visitor calls do not match Struson visitor calls"
        );
    }

    // Use a macro because otherwise would always have to use closure for deserializing action
    macro_rules! assert_deserialized {
        ($json:expr, $method:ident, $expected_visited:expr) => {
            assert_deserialized!($json, |d, v| { d.$method(v) }, $expected_visited);
        };
        // This syntax emulates a closure: |d, v| { ... }
        ($json:expr, |$deserializer:ident, $visitor:ident| $deserializing_block:block, $expected_visited:expr) => {
            assert_deserialized!(
                $json,
                EnumVariantHandling::Unit,
                |$deserializer, $visitor| $deserializing_block,
                $expected_visited
            );
        };
        // This syntax emulates a closure: |d, v| { ... }
        ($json:expr, $enum_variant_handling:expr, |$deserializer:ident, $visitor:ident| $deserializing_block:block, $expected_visited:expr) => {
            assert_deserialized_enum(
                $json,
                $enum_variant_handling,
                |$deserializer, $visitor| $deserializing_block,
                &$expected_visited,
            );
        };
    }

    fn assert_deserialized_enum_serde_json<
        F: Fn(
            &mut serde_json::Deserializer<StrRead<'_>>,
            &mut TrackingVisitor,
        ) -> Result<(), serde_json::Error>,
    >(
        json: &str,
        enum_variant_handling: EnumVariantHandling,
        deserializing_function: F,
        expected_visited: &[Visited],
    ) {
        let mut deserializer = serde_json::Deserializer::from_str(json);
        let mut visitor = TrackingVisitor::new(enum_variant_handling);
        deserializing_function(&mut deserializer, &mut visitor).unwrap();
        deserializer.end().unwrap();

        // Normalize Visited types since JsonReaderDeserializer does not support borrowed strings and bytes
        // with lifetime 'de, but serde_json does
        let visited: Vec<Visited> = visitor
            .visited
            .into_iter()
            .map(|v| match v {
                Visited::BorrowedStr(s) => Visited::Str(s),
                Visited::BorrowedBytes(b) => Visited::Bytes(b),
                v => v,
            })
            .collect();

        // Normalize expected Visited types because serde_json does not use `visit_byte_buf` or `visit_string`
        let expected_visited: Vec<Visited> = expected_visited
            .iter()
            .map(|v| match v.clone() {
                Visited::String(s) => Visited::Str(s),
                Visited::ByteBuf(b) => Visited::Bytes(b),
                v => v,
            })
            .collect();

        assert_eq!(
            expected_visited, visited,
            "expected visitor calls do not match serde_json visitor calls"
        );
    }

    /// Asserts that both the deserializer from this module as well as serde_json's deserializer
    /// call the visitor in the same way
    macro_rules! assert_deserialized_cmp {
        ($json:expr, $method:ident, $expected_visited:expr) => {
            assert_deserialized_cmp!($json, |d, v| { d.$method(v) }, $expected_visited);
        };
        // This syntax emulates a closure: |d, v| { ... }
        ($json:expr, |$deserializer:ident, $visitor:ident| $deserializing_block:block, $expected_visited:expr) => {
            assert_deserialized_cmp!(
                $json,
                EnumVariantHandling::Unit,
                |$deserializer, $visitor| $deserializing_block,
                $expected_visited
            );
        };
        // This syntax emulates a closure: |d, v| { ... }
        ($json:expr, $enum_variant_handling:expr, |$deserializer:ident, $visitor:ident| $deserializing_block:block, $expected_visited:expr) => {
            assert_deserialized_enum(
                $json,
                $enum_variant_handling,
                |$deserializer, $visitor| $deserializing_block,
                &$expected_visited,
            );

            assert_deserialized_enum_serde_json(
                $json,
                $enum_variant_handling,
                |$deserializer, $visitor| $deserializing_block,
                &$expected_visited,
            );
        };
    }

    macro_rules! assert_deserialize_error {
        ($json:expr, $method:ident, $expected_pattern:pat_param => $assertion:expr) => {
            assert_deserialize_error!($json, EnumVariantHandling::Unit, |d, v| { d.$method(v) }, $expected_pattern => $assertion)
        };
        // This syntax emulates a closure: |d, v| { ... }
        ($json:expr, $enum_variant_handling:expr, |$deserializer:ident, $visitor:ident| $deserializing_block:block, $expected_pattern:pat_param => $assertion:expr) => {
            let mut json_reader = JsonStreamReader::new($json.as_bytes());
            let mut $deserializer = JsonReaderDeserializer::new(&mut json_reader);
            let $visitor = &mut TrackingVisitor::new($enum_variant_handling);
            let result = $deserializing_block;
            match result {
                Err($expected_pattern) => $assertion,
                r => panic!("Unexpected result for '{}': {r:?}", $json),
            }
        };
    }

    macro_rules! assert_parse_number_error {
        ($method:ident, [$($json:expr),+]) => {
            for json in [$($json),+] {
                assert_deserialize_error!(json, $method, DeserializerError::InvalidNumber(_) => {});
            }
        };
    }

    #[test]
    fn deserialize_any() {
        assert_deserialized_cmp!(
            "[1]",
            deserialize_any,
            [Visited::SeqStart, Visited::U64(1), Visited::SeqEnd]
        );
        assert_deserialized_cmp!(
            r#"{"a": 1}"#,
            deserialize_any,
            [
                Visited::MapStart,
                Visited::Str("a".to_owned()),
                Visited::U64(1),
                Visited::MapEnd
            ]
        );
        assert_deserialized_cmp!(
            "\"test\"",
            deserialize_any,
            // This differs for serde_json which actually deserializes a borrowed `str`
            [Visited::String("test".to_owned())]
        );
        assert_deserialized_cmp!("true", deserialize_any, [Visited::Bool(true)]);
        assert_deserialized_cmp!("null", deserialize_any, [Visited::Unit]);

        assert_deserialized_cmp!("-1", deserialize_any, [Visited::I64(-1)]);
        assert_deserialized_cmp!("1", deserialize_any, [Visited::U64(1)]);
        // Note: Does not use assert_deserialized_cmp! because serde_json reads this as f64
        assert_deserialized!(
            &(i64::MIN as i128 - 1).to_string(),
            deserialize_any,
            [Visited::I128(i64::MIN as i128 - 1)]
        );
        // Note: Does not use assert_deserialized_cmp! because serde_json reads this as f64
        assert_deserialized!(
            &(u64::MAX as u128 + 1).to_string(),
            deserialize_any,
            [Visited::U128(u64::MAX as u128 + 1)]
        );
        assert_deserialized_cmp!("1.0", deserialize_any, [Visited::F64(1.0)]);
        assert_deserialized_cmp!("1e1", deserialize_any, [Visited::F64(1e1)]);
        assert_deserialized_cmp!("1E1", deserialize_any, [Visited::F64(1e1)]);

        assert_parse_number_error!(
            deserialize_any,
            [
                // u128::MIN - 1
                "-170141183460469231731687303715884105729",
                // u128::MAX + 1
                "340282366920938463463374607431768211456"
            ]
        );
    }

    #[test]
    fn deserialize_bool() {
        assert_deserialized_cmp!("true", deserialize_bool, [Visited::Bool(true)]);
        assert_deserialized_cmp!("false", deserialize_bool, [Visited::Bool(false)]);

        assert_deserialize_error!(
            "1",
            deserialize_bool,
            DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
                assert_eq!(ValueType::Boolean, expected);
                assert_eq!(ValueType::Number, actual);
            }
        );
    }

    /// Important: Does not work for i128 and u128 (because cannot calculate + 1 and - 1
    /// for their MAX respectively MIN value)
    macro_rules! assert_min_max_deserialization {
        ($method:ident, $type:ident, $visited:ident) => {
            // Note: Does not use assert_deserialized_cmp! because serde_json only deserializes
            // as u64, i64 and f64 depending on the format of the number, ignoring the originally
            // requested type
            let min = $type::MIN;
            assert_deserialized!(&min.to_string(), $method, [Visited::$visited(min)]);
            let max = $type::MAX;
            assert_deserialized!(&max.to_string(), $method, [Visited::$visited(max)]);

            // MIN - 1
            let min_off = ((min as i128) - 1).to_string();
            // MAX + 1
            let max_off = ((max as i128) + 1).to_string();
            assert_parse_number_error!($method, [&min_off, &max_off]);

            assert_deserialize_error!(
                "true",
                $method,
                DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
                    assert_eq!(ValueType::Number, expected);
                    assert_eq!(ValueType::Boolean, actual);
                }
            );
        };
    }

    #[test]
    fn deserialize_i8() {
        assert_min_max_deserialization!(deserialize_i8, i8, I8);
    }

    #[test]
    fn deserialize_i16() {
        assert_min_max_deserialization!(deserialize_i16, i16, I16);
    }

    #[test]
    fn deserialize_i32() {
        assert_min_max_deserialization!(deserialize_i32, i32, I32);
    }

    #[test]
    fn deserialize_i64() {
        assert_min_max_deserialization!(deserialize_i64, i64, I64);

        // serde_json deserializes all negative numbers as i64 by default
        assert_deserialized_cmp!("-3", deserialize_i64, [Visited::I64(-3)]);
    }

    #[test]
    fn deserialize_i128() {
        assert_deserialized_cmp!(
            &i128::MIN.to_string(),
            deserialize_i128,
            [Visited::I128(i128::MIN)]
        );
        assert_deserialized_cmp!(
            &i128::MAX.to_string(),
            deserialize_i128,
            [Visited::I128(i128::MAX)]
        );

        assert_parse_number_error!(
            deserialize_i128,
            [
                // MIN - 1
                "-170141183460469231731687303715884105729",
                // MAX + 1
                "170141183460469231731687303715884105728"
            ]
        );

        assert_deserialize_error!(
            "true",
            deserialize_i128,
            DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
                assert_eq!(ValueType::Number, expected);
                assert_eq!(ValueType::Boolean, actual);
            }
        );
    }

    #[test]
    fn deserialize_u8() {
        assert_min_max_deserialization!(deserialize_u8, u8, U8);
    }

    #[test]
    fn deserialize_u16() {
        assert_min_max_deserialization!(deserialize_u16, u16, U16);
    }

    #[test]
    fn deserialize_u32() {
        assert_min_max_deserialization!(deserialize_u32, u32, U32);
    }

    #[test]
    fn deserialize_u64() {
        assert_min_max_deserialization!(deserialize_u64, u64, U64);

        // serde_json deserializes all unsigned numbers as u64 by default
        assert_deserialized_cmp!("3", deserialize_u64, [Visited::U64(3)]);
    }

    #[test]
    fn deserialize_u128() {
        assert_deserialized_cmp!(
            &u128::MIN.to_string(),
            deserialize_u128,
            [Visited::U128(u128::MIN)]
        );
        assert_deserialized_cmp!(
            &u128::MAX.to_string(),
            deserialize_u128,
            [Visited::U128(u128::MAX)]
        );

        assert_parse_number_error!(
            deserialize_u128,
            [
                // MIN - 1
                "-1",
                // MAX + 1
                "340282366920938463463374607431768211456"
            ]
        );

        assert_deserialize_error!(
            "true",
            deserialize_u128,
            DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
                assert_eq!(ValueType::Number, expected);
                assert_eq!(ValueType::Boolean, actual);
            }
        );
    }

    #[test]
    fn deserialize_f32() {
        // Note: Does not use assert_deserialized_cmp! because serde_json calls visit_f64
        assert_deserialized!("-0.0", deserialize_f32, [Visited::F32(-0.0)]);
        assert_deserialized!("123e-45", deserialize_f32, [Visited::F32(123e-45)]);

        assert_deserialized!(
            &f32::MIN_POSITIVE.to_string(),
            deserialize_f32,
            [Visited::F32(f32::MIN_POSITIVE)]
        );
        assert_deserialized!(
            &f32::MIN.to_string(),
            deserialize_f32,
            [Visited::F32(f32::MIN)]
        );
        assert_deserialized!(
            &f32::MAX.to_string(),
            deserialize_f32,
            [Visited::F32(f32::MAX)]
        );

        assert_deserialize_error!(
            "true",
            deserialize_f32,
            DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
                assert_eq!(ValueType::Number, expected);
                assert_eq!(ValueType::Boolean, actual);
            }
        );
    }

    #[test]
    fn deserialize_f64() {
        assert_deserialized_cmp!("-0.0", deserialize_f64, [Visited::F64(-0.0)]);
        assert_deserialized_cmp!("123e-45", deserialize_f64, [Visited::F64(123e-45)]);

        fn assert_deserialized_f64(json: &str, value: f64) {
            let mut json_reader = JsonStreamReader::new_custom(
                json.as_bytes(),
                ReaderSettings {
                    // Must disable number restriction because f64::MIN_POSITIVE, f64::MIN and f64::MAX
                    // are not allowed by default because they are too large
                    restrict_number_values: false,
                    ..Default::default()
                },
            );
            let mut deserializer = JsonReaderDeserializer::new(&mut json_reader);
            let mut visitor = TrackingVisitor::new(EnumVariantHandling::Unit);
            deserializer.deserialize_f64(&mut visitor).unwrap();
            json_reader.consume_trailing_whitespace().unwrap();

            assert_eq!(vec![Visited::F64(value)], visitor.visited);

            // Note: Does not compare with serde_json because it fails parsing f64::MIN and f64::MAX strings
        }

        assert_deserialized_f64(&f64::MIN_POSITIVE.to_string(), f64::MIN_POSITIVE);
        assert_deserialized_f64("4.9E-324", 4.9E-324);

        assert_deserialized_f64(&f64::MIN.to_string(), f64::MIN);
        assert_deserialized_f64(&f64::MAX.to_string(), f64::MAX);
        assert_deserialized_f64("-1.7976931348623157E308", f64::MIN);
        assert_deserialized_f64("1.7976931348623157E308", f64::MAX);

        assert_deserialize_error!(
            "true",
            deserialize_f64,
            DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
                assert_eq!(ValueType::Number, expected);
                assert_eq!(ValueType::Boolean, actual);
            }
        );
    }

    duplicate::duplicate! {
        [
            method visited_type;
            [deserialize_char] [Str];
            [deserialize_str] [Str];
            [deserialize_string] [String];
            [deserialize_identifier] [Str];
        ]
        #[test]
        fn method() {
            assert_deserialized_cmp!("\"\"", method, [Visited::visited_type("".to_owned())]);
            assert_deserialized_cmp!("\"a\"", method, [Visited::visited_type("a".to_owned())]);
            assert_deserialized_cmp!(
                "\"\\u0000\"",
                method,
                [Visited::visited_type("\0".to_owned())]
            );
            assert_deserialized_cmp!(
                "\"\u{10FFFF}\"",
                method,
                [Visited::visited_type("\u{10FFFF}".to_owned())]
            );

            assert_deserialize_error!(
                "true",
                method,
                DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
                    assert_eq!(ValueType::String, expected);
                    assert_eq!(ValueType::Boolean, actual);
                }
            );
        }
    }

    duplicate::duplicate! {
        [
            method visited_type;
            [deserialize_bytes] [Bytes];
            [deserialize_byte_buf] [ByteBuf];
        ]
        #[test]
        fn method() {
            assert_deserialized_cmp!("\"\"", method, [Visited::visited_type(vec![])]);
            assert_deserialized_cmp!("\"a\"", method, [Visited::visited_type("a".as_bytes().to_owned())]);
            assert_deserialized_cmp!("\"\\u0000\"", method, [Visited::visited_type("\0".as_bytes().to_owned())]);
            assert_deserialized_cmp!("\"\u{10FFFF}\"", method, [Visited::visited_type("\u{10FFFF}".as_bytes().to_owned())]);

            assert_deserialized_cmp!("[1, 2]", method, [Visited::SeqStart, Visited::U64(1), Visited::U64(2), Visited::SeqEnd]);
            // This just documents the current behavior; validation that array items are numbers might be added later
            assert_deserialized_cmp!("[true]", method, [Visited::SeqStart, Visited::Bool(true), Visited::SeqEnd]);

            // Unlike serde_json malformed UTF-8 strings are not supported
            assert_deserialize_error!(
                "\"\\uD800\"",
                method,
                DeserializerError::ReaderError(ReaderError::SyntaxError(e)) => {
                    assert_eq!(SyntaxErrorKind::UnpairedSurrogatePairEscapeSequence, e.kind);
                }
            );
            let mut json_reader = JsonStreamReader::new(b"\"\x80\"" as &[u8]); // malformed single byte
            let mut deserializer = JsonReaderDeserializer::new(&mut json_reader);
            let visitor = &mut TrackingVisitor::new(EnumVariantHandling::Unit);
            let result = deserializer.method(visitor);
            match result {
                Err(DeserializerError::ReaderError(ReaderError::IoError { error, location })) => {
                    assert_eq!(ErrorKind::InvalidData, error.kind());
                    assert_eq!("invalid UTF-8 data", error.to_string());
                    assert_eq!(JsonErrorLocation {
                        path: "$".to_owned(),
                        line: 0,
                        column: 1,
                    }, location);
                }
                r => panic!("Unexpected result: {r:?}"),
            }

            assert_deserialize_error!(
                "true",
                method,
                DeserializerError::Custom(message) => {
                    assert_eq!("invalid type: bool, expected custom-test-value", message);
                }
            );
        }
    }

    #[test]
    fn deserialize_option() {
        assert_deserialized_cmp!("null", deserialize_option, [Visited::None]);
        assert_deserialized_cmp!(
            "true",
            deserialize_option,
            [Visited::SomeStart, Visited::Bool(true), Visited::SomeEnd]
        );
    }

    #[test]
    fn deserialize_unit() {
        assert_deserialized_cmp!("null", deserialize_unit, [Visited::Unit]);

        assert_deserialize_error!(
            "true",
            deserialize_unit,
            DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
                assert_eq!(ValueType::Null, expected);
                assert_eq!(ValueType::Boolean, actual);
            }
        );
    }

    #[test]
    fn deserialize_unit_struct() {
        assert_deserialized_cmp!(
            "null",
            |d, v| { d.deserialize_unit_struct("name", v) },
            [Visited::Unit]
        );

        assert_deserialize_error!(
            "true",
            EnumVariantHandling::Unit,
            |d, v| { d.deserialize_unit_struct("name", v) },
            DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
                assert_eq!(ValueType::Null, expected);
                assert_eq!(ValueType::Boolean, actual);
            }
        );
    }

    #[test]
    fn deserialize_newtype_struct() {
        assert_deserialized_cmp!(
            "true",
            |d, v| { d.deserialize_newtype_struct("name", v) },
            [
                Visited::NewtypeStructStart,
                Visited::Bool(true),
                Visited::NewtypeStructEnd
            ]
        );
    }

    #[test]
    fn deserialize_seq() {
        assert_deserialized_cmp!("[]", deserialize_seq, [Visited::SeqStart, Visited::SeqEnd]);
        assert_deserialized_cmp!(
            "[1]",
            deserialize_seq,
            [Visited::SeqStart, Visited::U64(1), Visited::SeqEnd]
        );
        assert_deserialized_cmp!(
            "[1, 2]",
            deserialize_seq,
            [
                Visited::SeqStart,
                Visited::U64(1),
                Visited::U64(2),
                Visited::SeqEnd
            ]
        );

        assert_deserialize_error!(
            "true",
            deserialize_seq,
            DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
                assert_eq!(ValueType::Array, expected);
                assert_eq!(ValueType::Boolean, actual);
            }
        );
    }

    #[test]
    fn deserialize_tuple() {
        assert_deserialized_cmp!(
            "[]",
            |d, v| { d.deserialize_tuple(0, v) },
            [Visited::SeqStart, Visited::SeqEnd]
        );

        assert_deserialized_cmp!(
            "[1]",
            |d, v| { d.deserialize_tuple(1, v) },
            [Visited::SeqStart, Visited::U64(1), Visited::SeqEnd]
        );

        assert_deserialized_cmp!(
            "[1, 2]",
            |d, v| { d.deserialize_tuple(2, v) },
            [
                Visited::SeqStart,
                Visited::U64(1),
                Visited::U64(2),
                Visited::SeqEnd
            ]
        );

        assert_deserialize_error!(
            "[1]",
            EnumVariantHandling::Unit,
            |d, v| { d.deserialize_tuple(0, v) },
            DeserializerError::Custom(message) => {
                assert_eq!("invalid length 1, expected array of length 0", message);
            }
        );
        assert_deserialize_error!(
            "[]",
            EnumVariantHandling::Unit,
            |d, v| { d.deserialize_tuple(1, v) },
            DeserializerError::Custom(message) => {
                assert_eq!("invalid length 0, expected array of length 1", message);
            }
        );

        assert_deserialize_error!(
            "true",
            EnumVariantHandling::Unit,
            |d, v| { d.deserialize_tuple(1, v) },
            DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
                assert_eq!(ValueType::Array, expected);
                assert_eq!(ValueType::Boolean, actual);
            }
        );
    }

    #[test]
    fn deserialize_tuple_struct() {
        assert_deserialized_cmp!(
            "[]",
            |d, v| { d.deserialize_tuple_struct("name", 0, v) },
            [Visited::SeqStart, Visited::SeqEnd]
        );

        assert_deserialized_cmp!(
            "[1]",
            |d, v| { d.deserialize_tuple_struct("name", 1, v) },
            [Visited::SeqStart, Visited::U64(1), Visited::SeqEnd]
        );

        assert_deserialized_cmp!(
            "[1, 2]",
            |d, v| { d.deserialize_tuple_struct("name", 2, v) },
            [
                Visited::SeqStart,
                Visited::U64(1),
                Visited::U64(2),
                Visited::SeqEnd
            ]
        );

        assert_deserialize_error!(
            "[1]",
            EnumVariantHandling::Unit,
            |d, v| { d.deserialize_tuple_struct("name", 0, v) },
            DeserializerError::Custom(message) => {
                assert_eq!("invalid length 1, expected array of length 0", message);
            }
        );
        assert_deserialize_error!(
            "[]",
            EnumVariantHandling::Unit,
            |d, v| { d.deserialize_tuple_struct("name", 1, v) },
            DeserializerError::Custom(message) => {
                assert_eq!("invalid length 0, expected array of length 1", message);
            }
        );

        assert_deserialize_error!(
            "true",
            EnumVariantHandling::Unit,
            |d, v| { d.deserialize_tuple_struct("name", 1, v) },
            DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
                assert_eq!(ValueType::Array, expected);
                assert_eq!(ValueType::Boolean, actual);
            }
        );
    }

    mod deserialize_map {
        use serde::de::MapAccess;

        use super::*;

        #[test]
        fn deserialize() {
            assert_deserialized_cmp!("{}", deserialize_map, [Visited::MapStart, Visited::MapEnd]);
            assert_deserialized_cmp!(
                r#"{"a": 1}"#,
                deserialize_map,
                [
                    Visited::MapStart,
                    Visited::Str("a".to_owned()),
                    Visited::U64(1),
                    Visited::MapEnd
                ]
            );
            assert_deserialized_cmp!(
                r#"{"1": 1, "true": 2}"#,
                deserialize_map,
                [
                    Visited::MapStart,
                    Visited::Str("1".to_owned()),
                    Visited::U64(1),
                    Visited::Str("true".to_owned()),
                    Visited::U64(2),
                    Visited::MapEnd
                ]
            );
            // Duplicate key
            assert_deserialized_cmp!(
                r#"{"a": 1, "a": 2}"#,
                deserialize_map,
                [
                    Visited::MapStart,
                    Visited::Str("a".to_owned()),
                    Visited::U64(1),
                    Visited::Str("a".to_owned()),
                    Visited::U64(2),
                    Visited::MapEnd
                ]
            );

            assert_deserialize_error!(
                "true",
                deserialize_map,
                DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
                    assert_eq!(ValueType::Object, expected);
                    assert_eq!(ValueType::Boolean, actual);
                }
            );
        }

        #[test]
        fn string_key_conversion() {
            // Maybe these macros are too verbose and complex for the functionality they provide
            macro_rules! assert_deserialized_key {
                (
                    // The content of the object key (without enclosing `"`)
                    $key_content:expr,
                    // Creates the reader, which is backing the deserializer (can also be the deserializer itself for serde_json)
                    |$json:ident| $reader_factory:expr,
                    // Creates the deserializer from the reader
                    |$json_reader:ident| $deserializer_factory:expr,
                    // Performs deserialization of the key
                    |$deserializer:ident, $visitor:ident| $deserializing_block:block,
                    // Handles the result of `next_key_seed`
                    |$key_result:ident, $map:ident| $key_result_handler:block,
                    // Performs finalization after the deserialization, e.g. consuming trailing whitespace of the JSON
                    $finalizing_action:block,
                    // Handles the result of `deserialize_map`
                    |$map_result:ident, $visited:ident| $map_result_handler:block
                ) => {{
                    let $json = "{\"".to_owned() + $key_content + "\": true}";
                    #[allow(unused_mut)] // for serde_json where `$json_reader == deserializer`
                    let mut $json_reader = $reader_factory;
                    let mut deserializer = $deserializer_factory;

                    struct MapVisitor<'a> {
                        key_visitor: &'a mut TrackingVisitor,
                    }
                    impl<'de> Visitor<'de> for &mut MapVisitor<'_> {
                        type Value = ();

                        fn expecting(
                            &self,
                            formatter: &mut std::fmt::Formatter,
                        ) -> std::fmt::Result {
                            write!(formatter, "map")
                        }

                        fn visit_map<A: serde::de::MapAccess<'de>>(
                            self,
                            mut $map: A,
                        ) -> Result<Self::Value, A::Error> {
                            struct KeyDeserialize<'a> {
                                key_visitor: &'a mut TrackingVisitor,
                            }
                            impl<'de> DeserializeSeed<'de> for &mut KeyDeserialize<'_> {
                                type Value = ();

                                fn deserialize<D: Deserializer<'de>>(
                                    self,
                                    $deserializer: D,
                                ) -> Result<Self::Value, D::Error> {
                                    let $visitor = &mut *self.key_visitor;
                                    $deserializing_block
                                }
                            }
                            let $key_result = $map.next_key_seed(&mut KeyDeserialize {
                                key_visitor: &mut *self.key_visitor,
                            });
                            $key_result_handler
                        }
                    }

                    let mut key_visitor = TrackingVisitor::new(EnumVariantHandling::Unit);
                    let $map_result = deserializer.deserialize_map(&mut MapVisitor {
                        key_visitor: &mut key_visitor,
                    });
                    let $visited = key_visitor.visited;
                    $map_result_handler;
                }};
            }

            macro_rules! assert_deserialized_key_cmp {
                (
                    // The content of the object key (without enclosing `"`)
                    $key_content:expr,
                    // Performs deserialization of the key
                    |$deserializer:ident, $visitor:ident| $deserializing_block:block,
                    // Tested library display name (Struson or serde_json); used for assertion messages
                    $library_name:ident,
                    // Handles the result of `next_key_seed`
                    |$key_result:ident, $map:ident| $key_result_handler:block,
                    // Whether to perform finalization after the deserialization (should only be `true` for successful deserialization)
                    $perform_finalization:expr,
                    // Handles the result of `deserialize_map`
                    |$map_result:ident, $visited:ident| $map_result_handler_struson:block, $map_result_handler_serde_json:block
                ) => {{
                    {
                        const $library_name: &str = "Struson";
                        assert_deserialized_key!(
                            $key_content,
                            |json| JsonStreamReader::new(json.as_bytes()),
                            |json_reader| JsonReaderDeserializer::new(&mut json_reader),
                            |$deserializer, $visitor| $deserializing_block,
                            |$key_result, $map| $key_result_handler,
                            {
                                if $perform_finalization {
                                    json_reader.consume_trailing_whitespace()?;
                                }
                            },
                            |$map_result, $visited| $map_result_handler_struson
                        );
                    }

                    {
                        const $library_name: &str = "serde_json";
                        assert_deserialized_key!(
                            $key_content,
                            |json| serde_json::Deserializer::from_str(&json),
                            // Reader is already the Deserializer
                            |json_reader| json_reader,
                            |$deserializer, $visitor| $deserializing_block,
                            |$key_result, $map| $key_result_handler,
                            {
                                if $perform_finalization {
                                    json_reader.end()?;
                                }
                            },
                            |$map_result, $visited| $map_result_handler_serde_json
                        );
                    }
                }};
            }

            macro_rules! assert_deserialized_key_success {
                ($key_content:expr, |$deserializer:ident, $visitor:ident| $deserializing_block:block, $expected_visited:expr) => {{
                    assert_deserialized_key_cmp!(
                        $key_content,
                        |$deserializer, $visitor| $deserializing_block,
                        LIBRARY_NAME,
                        |key_result, map| {
                            key_result.expect(&format!("key deserialization should have been successful for {LIBRARY_NAME}"));
                            // Read hardcoded map entry value `true`
                            assert_eq!(true, map.next_value::<bool>()?);

                            assert!(map.next_key::<String>()?.is_none());
                            Ok(())
                        },
                        true, // perform finalization
                        |map_result, visited|
                        // Struson assertions
                        {
                            map_result.expect(&format!("map deserialization should have been successful for {LIBRARY_NAME}"));
                            assert_eq!(
                                &$expected_visited as &[Visited], visited,
                                "expected visitor calls do not match {LIBRARY_NAME} visitor calls"
                            );
                        },
                        // serde_json assertions
                        {
                            // Normalize expected Visited types since serde_json only supports u64, i64 and f64
                            // serde_json parses only depending on format of JSON number, regardless of called `deserialize_...` method;
                            // for simplicity only cover the cases used by the tests
                            let expected_visited: Vec<Visited> = $expected_visited
                                .into_iter()
                                .map(|v| match v {
                                    Visited::U8(n) => Visited::U64(n.into()),
                                    Visited::I8(n) => Visited::U64(n.try_into().unwrap()),
                                    // Convert to string first to avoid for example f32 `1.2` becoming f64 `1.2000000476837158`
                                    Visited::F32(n) => Visited::F64(f64::from_str(&n.to_string()).unwrap()),
                                    v => v,
                                })
                                .collect();

                            // Normalize Visited types since JsonReaderDeserializer does not support borrowed strings and bytes
                            // with lifetime 'de, but serde_json does
                            let visited: Vec<Visited> = visited
                                .into_iter()
                                .map(|v| match v {
                                    Visited::BorrowedStr(s) => Visited::Str(s),
                                    Visited::BorrowedBytes(b) => Visited::Bytes(b),
                                    v => v,
                                })
                                .collect();

                            map_result.expect(&format!("map deserialization should have been successful for {LIBRARY_NAME}"));
                            assert_eq!(
                                expected_visited, visited,
                                "expected visitor calls do not match {LIBRARY_NAME} visitor calls"
                            );
                        }
                    );
                }};
            }

            macro_rules! assert_deserialized_key_error {
                ($key_content:expr, |$deserializer:ident, $visitor:ident| $deserializing_block:block, $err_pattern:pat_param => $err_assertion:expr) => {{
                    assert_deserialized_key_cmp!(
                        $key_content,
                        |$deserializer, $visitor| $deserializing_block,
                        LIBRARY_NAME,
                        |key_result, map| {
                            match key_result {
                                Err(e) => Err(e), // pass error to caller (and implicitly change T of Result<T, _>)
                                _ => panic!("Should have returned error for {LIBRARY_NAME}, but was: {key_result:?}"),
                            }
                        },
                        false, // don't perform finalization because JSON was not fully consumed
                        |map_result, _visited|
                        // Struson assertions
                        {
                            match map_result {
                                Err($err_pattern) => $err_assertion,
                                _ => panic!("Should have returned error for Struson, but was: {map_result:?}"),
                            }
                        },
                        // serde_json assertions
                        {
                            // Only assert that error occurred, but don't check implementation specific error message
                            assert!(map_result.is_err(), "Should have returned error for serde_json, but was: {map_result:?}")
                        }
                    );
                }};
            }

            assert_deserialized_key_success!(
                "true",
                |d, v| { d.deserialize_bool(v) },
                [Visited::Bool(true)]
            );
            assert_deserialized_key_success!(
                "false",
                |d, v| { d.deserialize_bool(v) },
                [Visited::Bool(false)]
            );
            assert_deserialized_key_success!("1", |d, v| { d.deserialize_i8(v) }, [Visited::I8(1)]);
            assert_deserialized_key_success!(
                "5",
                |d, v| { d.deserialize_u128(v) },
                [Visited::U128(5)]
            );
            assert_deserialized_key_success!(
                "1.2",
                |d, v| { d.deserialize_f32(v) },
                [Visited::F32(1.2)]
            );
            assert_deserialized_key_success!(
                "4.5e-6",
                |d, v| { d.deserialize_f64(v) },
                [Visited::F64(4.5e-6)]
            );
            assert_deserialized_key_success!(
                "true",
                |d, v| { d.deserialize_option(v) },
                [
                    Visited::SomeStart,
                    Visited::Str("true".to_owned()),
                    Visited::SomeEnd
                ]
            );
            assert_deserialized_key_success!(
                "abc",
                |d, v| { d.deserialize_bytes(v) },
                [Visited::Bytes("abc".as_bytes().to_owned())]
            );
            assert_deserialized_key_success!(
                "abc",
                |d, v| { d.deserialize_byte_buf(v) },
                [Visited::Bytes("abc".as_bytes().to_owned())]
            );

            assert_deserialized_key_success!(
                "abc",
                |d, v| { d.deserialize_newtype_struct("name", v) },
                [
                    Visited::NewtypeStructStart,
                    Visited::Str("abc".to_owned()),
                    Visited::NewtypeStructEnd
                ]
            );

            assert_deserialized_key_success!(
                "abc",
                |d, v| { d.deserialize_enum("name", &["abc"], v) },
                [
                    Visited::EnumStart,
                    Visited::Str("abc".to_owned()),
                    Visited::EnumEnd
                ]
            );

            // These all fall back to `visit_str`
            duplicate::duplicate! {
                [
                    method;
                    [deserialize_seq];
                    [deserialize_map];
                ]
                assert_deserialized_key_success!("abc", |d, v| {d.method(v)}, [Visited::Str("abc".to_owned())]);
            }

            // Currently `deserialize_ignored_any` calls `visit_str`; this matches serde_json's behavior,
            // but maybe `visit_none` would make more sense (and be consistent with JsonReaderDeserializer)
            assert_deserialized_key_success!(
                "abc",
                |d, v| { d.deserialize_ignored_any(v) },
                [Visited::Str("abc".to_owned())]
            );

            assert_deserialized_key_error!(
                "text",
                |d, v| { d.deserialize_bool(v) },
                DeserializerError::Custom(message) => assert_eq!("invalid type: string \"text\", expected custom-test-value", message)
            );

            assert_deserialized_key_error!(
                "text",
                |d, v| { d.deserialize_i32(v) },
                DeserializerError::InvalidNumber(message) => assert_eq!("invalid number: text", message)
            );
            assert_deserialized_key_error!(
                "NaN",
                |d, v| { d.deserialize_f32(v) },
                DeserializerError::InvalidNumber(message) => assert_eq!("invalid number: NaN", message)
            );
            // Deserializes as u128 here because for other number types this only fails for Struson but not serde_json
            // because serde_json ignores which exact `deserialize_...` was called and deserializes based on the JSON number format
            assert_deserialized_key_error!(
                "-5",
                |d, v| { d.deserialize_u128(v) },
                DeserializerError::InvalidNumber(message) => assert_eq!("number -5 cannot be parsed as desired type", message)
            );

            // Should validate that number is valid JSON number, even if normal parsing functions can parse it
            let number_str = "001";
            let _ = u32::from_str(number_str).unwrap(); // verify that test is implemented correctly
            assert_deserialized_key_error!(
                number_str,
                |d, v| { d.deserialize_u32(v) },
                DeserializerError::InvalidNumber(message) => assert_eq!(format!("invalid number: {number_str}"), message)
            );

            // Should validate that number is valid JSON number, even if normal parsing functions can parse it
            let number_str = ".1";
            let _ = f32::from_str(number_str).unwrap(); // verify that test is implemented correctly
            assert_deserialized_key_error!(
                number_str,
                |d, v| { d.deserialize_f32(v) },
                DeserializerError::InvalidNumber(message) => assert_eq!(format!("invalid number: {number_str}"), message)
            );
        }

        macro_rules! use_map_access {
            (|$map:ident| $map_access_consumer_block:block) => {
                let mut json_reader = JsonStreamReader::new(r#"{"key": "value"}"#.as_bytes());
                let mut deserializer = JsonReaderDeserializer::new(&mut json_reader);

                struct V;
                impl<'de> Visitor<'de> for V {
                    type Value = String;

                    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                        write!(formatter, "map")
                    }

                    fn visit_map<A: MapAccess<'de>>(
                        self,
                        mut $map: A,
                    ) -> Result<Self::Value, A::Error> {
                        $map_access_consumer_block
                    }
                }

                deserializer.deserialize_map(V).unwrap();
            };
        }

        #[test]
        #[should_panic(expected = "Incorrect usage: Cannot deserialize value when key is expected")]
        fn unexpected_value() {
            use_map_access!(|m| { m.next_value() });
        }

        #[test]
        #[should_panic(expected = "Incorrect usage: Cannot deserialize key when value is expected")]
        fn unexpected_key() {
            use_map_access!(|m| {
                m.next_key::<String>().unwrap().unwrap();
                m.next_key::<String>().unwrap().unwrap();
                Ok("".to_owned())
            });
        }

        #[test]
        #[should_panic(expected = "Incorrect usage: Did not deserialize trailing value")]
        fn end_missing_value() {
            use_map_access!(|m| {
                m.next_key::<String>().unwrap().unwrap();
                Ok("".to_owned())
            });
        }
    }

    #[test]
    fn deserialize_struct() {
        assert_deserialized_cmp!(
            "[]",
            |d, v| { d.deserialize_struct("name", &["a"], v) },
            [Visited::SeqStart, Visited::SeqEnd]
        );

        assert_deserialized_cmp!(
            "[1]",
            |d, v| { d.deserialize_struct("name", &["a"], v) },
            [Visited::SeqStart, Visited::U64(1), Visited::SeqEnd]
        );

        assert_deserialized_cmp!(
            "{}",
            |d, v| { d.deserialize_struct("name", &["a"], v) },
            [Visited::MapStart, Visited::MapEnd]
        );

        assert_deserialized_cmp!(
            r#"{"a": 1}"#,
            |d, v| { d.deserialize_struct("name", &["a"], v) },
            [
                Visited::MapStart,
                Visited::Str("a".to_owned()),
                Visited::U64(1),
                Visited::MapEnd
            ]
        );

        // Duplicate member name
        assert_deserialized_cmp!(
            r#"{"a": 1, "a": 2}"#,
            |d, v| { d.deserialize_struct("name", &["a"], v) },
            [
                Visited::MapStart,
                Visited::Str("a".to_owned()),
                Visited::U64(1),
                Visited::Str("a".to_owned()),
                Visited::U64(2),
                Visited::MapEnd
            ]
        );

        // Currently field names are not validated / unknown names are not detected
        assert_deserialized_cmp!(
            r#"{"unknown": 1}"#,
            |d, v| { d.deserialize_struct("name", &["a"], v) },
            [
                Visited::MapStart,
                Visited::Str("unknown".to_owned()),
                Visited::U64(1),
                Visited::MapEnd
            ]
        );

        assert_deserialize_error!(
            "true",
            EnumVariantHandling::Unit,
            |d, v| { d.deserialize_struct("name", &["a"], v) },
            DeserializerError::Custom(message) => {
                assert_eq!("invalid type: bool, expected custom-test-value", message);
            }
        );
    }

    #[test]
    fn deserialize_enum_object() {
        assert_deserialized_cmp!(
            r#"{"a": null}"#,
            EnumVariantHandling::Unit,
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            [
                Visited::EnumStart,
                Visited::Str("a".to_owned()),
                Visited::EnumEnd,
            ]
        );

        // The enum variant name is currently not validated
        assert_deserialized_cmp!(
            r#"{"unknown": null}"#,
            EnumVariantHandling::Unit,
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            [
                Visited::EnumStart,
                Visited::Str("unknown".to_owned()),
                Visited::EnumEnd,
            ]
        );

        assert_deserialize_error!(
            "{}",
            EnumVariantHandling::Unit,
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            DeserializerError::ReaderError(ReaderError::UnexpectedStructure{kind, ..}) => {
                assert_eq!(UnexpectedStructureKind::FewerElementsThanExpected, kind);
            }
        );

        assert_deserialize_error!(
            r#"{"a": null, "a": 1}"#,
            EnumVariantHandling::Unit,
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            DeserializerError::ReaderError(ReaderError::UnexpectedStructure{kind, ..}) => {
                assert_eq!(UnexpectedStructureKind::MoreElementsThanExpected, kind);
            }
        );

        assert_deserialize_error!(
            r#"{"a": 1}"#,
            EnumVariantHandling::Unit,
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
                assert_eq!(ValueType::Null, expected);
                assert_eq!(ValueType::Number, actual);
            }
        );

        assert_deserialized_cmp!(
            r#"{"a": 1}"#,
            EnumVariantHandling::Newtype,
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            [
                Visited::EnumStart,
                Visited::Str("a".to_owned()),
                Visited::U64(1),
                Visited::EnumEnd,
            ]
        );

        assert_deserialized_cmp!(
            r#"{"a": [1]}"#,
            EnumVariantHandling::Tuple(1),
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            [
                Visited::EnumStart,
                Visited::Str("a".to_owned()),
                Visited::SeqStart,
                Visited::U64(1),
                Visited::SeqEnd,
                Visited::EnumEnd,
            ]
        );

        assert_deserialize_error!(
            r#"{"a": []}"#,
            EnumVariantHandling::Tuple(1),
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            DeserializerError::Custom(message) => {
                assert_eq!("invalid length 0, expected array of length 1", message);
            }
        );

        assert_deserialize_error!(
            r#"{"a": 1}"#,
            EnumVariantHandling::Tuple(1),
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
                assert_eq!(ValueType::Array, expected);
                assert_eq!(ValueType::Number, actual);
            }
        );

        assert_deserialized_cmp!(
            r#"{"a": [1]}"#,
            EnumVariantHandling::Struct(&["f"]),
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            [
                Visited::EnumStart,
                Visited::Str("a".to_owned()),
                Visited::SeqStart,
                Visited::U64(1),
                Visited::SeqEnd,
                Visited::EnumEnd,
            ]
        );

        assert_deserialized_cmp!(
            r#"{"a": {"f": 1}}"#,
            EnumVariantHandling::Struct(&["f"]),
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            [
                Visited::EnumStart,
                Visited::Str("a".to_owned()),
                Visited::MapStart,
                Visited::Str("f".to_owned()),
                Visited::U64(1),
                Visited::MapEnd,
                Visited::EnumEnd,
            ]
        );

        // The struct field names are currently not validated
        assert_deserialized_cmp!(
            r#"{"a": {"unknown": 1}}"#,
            EnumVariantHandling::Struct(&["f"]),
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            [
                Visited::EnumStart,
                Visited::Str("a".to_owned()),
                Visited::MapStart,
                Visited::Str("unknown".to_owned()),
                Visited::U64(1),
                Visited::MapEnd,
                Visited::EnumEnd,
            ]
        );

        assert_deserialize_error!(
            r#"{"a": 1}"#,
            EnumVariantHandling::Struct(&["f"]),
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            DeserializerError::Custom(message) => {
                assert_eq!("invalid type: number, expected custom-test-value", message);
            }
        );

        assert_deserialize_error!(
            "true",
            EnumVariantHandling::Unit,
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            DeserializerError::Custom(message) => {
                assert_eq!("invalid type: bool, expected custom-test-value", message);
            }
        );
    }

    fn assert_ignored_enum_variant_panic(json: &str, consume_variant_name: bool) {
        let mut json_reader = JsonStreamReader::new(json.as_bytes());
        let mut deserializer = JsonReaderDeserializer::new(&mut json_reader);

        struct V {
            consume_variant_name: bool,
        }
        impl<'de> Visitor<'de> for V {
            type Value = ();

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(formatter, "enum")
            }

            fn visit_enum<A: serde::de::EnumAccess<'de>>(
                self,
                data: A,
            ) -> Result<Self::Value, A::Error> {
                // Bad implementation; in both cases does not deserialize variant value
                if self.consume_variant_name {
                    data.variant::<String>()?;
                }
                Ok(())
            }
        }
        deserializer
            .deserialize_enum(
                "name",
                &["a"],
                V {
                    consume_variant_name,
                },
            )
            .unwrap();
    }

    #[test]
    #[should_panic(expected = "Incorrect usage: Did not consume variant value")]
    fn deserialize_enum_object_variant_ignored() {
        assert_ignored_enum_variant_panic(r#"{"a": 1}"#, false);
    }

    #[test]
    #[should_panic(expected = "Incorrect usage: Did not consume variant value")]
    fn deserialize_enum_object_variant_value_ignored() {
        assert_ignored_enum_variant_panic(r#"{"a": 1}"#, true);
    }

    #[test]
    fn deserialize_enum_unit() {
        assert_deserialized_cmp!(
            "\"a\"",
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            [
                Visited::EnumStart,
                // This differs for serde_json which actually deserializes a borrowed `str`
                Visited::String("a".to_owned()),
                Visited::EnumEnd
            ]
        );

        // Currently variant names are not validated
        assert_deserialized_cmp!(
            "\"unknown\"",
            |d, v| { d.deserialize_enum("name", &["a"], v) },
            [
                Visited::EnumStart,
                // This differs for serde_json which actually deserializes a borrowed `str`
                Visited::String("unknown".to_owned()),
                Visited::EnumEnd
            ]
        );

        fn assert_enum_variant_error(
            enum_variant_handling: EnumVariantHandling,
            expected_error_message: &str,
        ) {
            assert_deserialize_error!(
                "\"a\"",
                enum_variant_handling,
                |d, v| {d.deserialize_enum("name", &["a"], v)},
                DeserializerError::Custom(message) => assert_eq!(expected_error_message, message)
            );
        }

        assert_enum_variant_error(
            EnumVariantHandling::Newtype,
            "invalid type: unit variant, expected newtype variant",
        );
        assert_enum_variant_error(
            EnumVariantHandling::Tuple(1),
            "invalid type: unit variant, expected tuple variant",
        );
        assert_enum_variant_error(
            EnumVariantHandling::Struct(&["a"]),
            "invalid type: unit variant, expected struct variant",
        );
    }

    #[test]
    #[should_panic(expected = "Incorrect usage: Did not consume variant value")]
    fn deserialize_enum_unit_variant_ignored() {
        assert_ignored_enum_variant_panic("\"a\"", false);
    }

    #[test]
    #[should_panic(expected = "Incorrect usage: Did not consume variant value")]
    fn deserialize_enum_unit_variant_value_ignored() {
        assert_ignored_enum_variant_panic("\"a\"", true);
    }

    #[test]
    fn deserialize_ignored_any() {
        let json_data = ["null", "true", "1", "\"test\"", "[]", "{}"];
        for json in json_data {
            assert_deserialized_cmp!(json, deserialize_ignored_any, [Visited::Unit]);
        }
    }

    #[test]
    fn nesting_limit() {
        #[derive(Deserialize, PartialEq, Debug)]
        struct Nested {
            n: Box<Option<Nested>>,
        }

        // Mix Vec and struct to make sure depth is decreased again when ending JSON array or object
        fn deserialize_custom_max_depth(json: &str) -> Result<Vec<Vec<Nested>>, DeserializerError> {
            let mut json_reader = JsonStreamReader::new(json.as_bytes());
            let mut deserializer =
                JsonReaderDeserializer::new_with_custom_nesting_limit(&mut json_reader, 4);
            Deserialize::deserialize(&mut deserializer)
        }

        let value =
            deserialize_custom_max_depth(r#"[[], [{"n": null}], [{"n": {"n": null}}]]"#).unwrap();
        assert_eq!(
            vec![
                vec![],
                vec![Nested { n: Box::new(None) }],
                vec![Nested {
                    n: Box::new(Some(Nested { n: Box::new(None) }))
                }]
            ],
            value
        );

        match deserialize_custom_max_depth(r#"[[{"n": {"n": {"n": null}}}]]"#) {
            Err(DeserializerError::MaxNestingDepthExceeded(max_depth)) => {
                assert_eq!(4, max_depth);
            }
            r => panic!("Unexpected result: {r:?}"),
        }

        fn deserialize_default_map_depth(json: &str) -> Result<Nested, DeserializerError> {
            let mut json_reader = JsonStreamReader::new(json.as_bytes());
            let mut deserializer = JsonReaderDeserializer::new(&mut json_reader);
            Deserialize::deserialize(&mut deserializer)
        }

        let mut expected_depth = DEFAULT_MAX_NESTING_DEPTH as usize;
        let json = format!(
            "{}null{}",
            r#"{"n":"#.repeat(expected_depth),
            "}".repeat(expected_depth)
        );
        let mut value = deserialize_default_map_depth(&json).unwrap();
        let mut depth = 1;
        while let Some(nested) = *value.n {
            value = nested;
            depth += 1;
        }
        assert_eq!(expected_depth, depth);

        expected_depth += 1;
        let json = format!(
            "{}null{}",
            r#"{"n":"#.repeat(expected_depth),
            "}".repeat(expected_depth)
        );
        match deserialize_default_map_depth(&json) {
            Err(DeserializerError::MaxNestingDepthExceeded(max_depth)) => {
                assert_eq!((expected_depth - 1) as u32, max_depth);
            }
            r => panic!("Unexpected result: {r:?}"),
        }
    }
}
