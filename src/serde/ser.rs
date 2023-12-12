use std::fmt::Display;

use crate::writer::{FiniteNumber, FloatingPointNumber, JsonNumberError, JsonWriter};

use serde::ser::{Impossible, Serialize, Serializer};
use thiserror::Error;

// Implementation based on:
// - https://serde.rs/impl-serializer.html
// - https://github.com/serde-rs/json/blob/v1.0.107/src/ser.rs
//   (trying to match it as close as possible)

type IoError = std::io::Error;

/// Error which occurred while serializing a value
#[non_exhaustive]
#[derive(Error, Debug)]
pub enum SerializerError {
    /// A custom error, normally created by the `SerializerError::custom` function
    ///
    /// The data of this enum variant is a message describing the error.
    #[error("{0}")]
    Custom(String),
    /// An IO error occurred while writing
    #[error("IO error: {0}")]
    IoError(#[from] IoError),
    /// A number value is not a valid JSON number
    ///
    /// The data of this enum variant is a message explaining why the number is not valid.
    #[error("invalid number: {0}")]
    InvalidNumber(String),
    /// An incorrect number of elements was serialized
    ///
    /// This error is created when the claimed expected number of elements or fields passed
    /// to compound value serialization methods such as `JsonWriterSerializer::serialize_struct`
    /// does not match the actual number of serialized elements or fields.
    /*
     * Note: Arguably could also panic instead, since this is probably in most cases caused
     * by incorrect usage, but maybe there are also cases where a (untrusted) user can influence
     * the element count number, so in that case an error instead of a panic would be safer
     */
    #[error("incorrect elements count, expected {expected} but got {actual}")]
    IncorrectElementsCount {
        /// The expected number of elements
        ///
        /// This value is provided when starting a compound value, for example when calling
        /// `JsonWriterSerializer::serialize_struct`.
        expected: usize,
        /// The actual number of serialized elements
        ///
        /// When more elements than expected are encountered serialization fails fast. In that
        /// case the `actual` value will just be `expected + 1` instead of the actual number
        /// of elements which would have been serialized in total.
        actual: usize,
    },
    /// An error which indicates that an unsupported map key was serialized
    ///
    /// This error is created when `JsonWriterSerializer::serialize_map` is used to serialize
    /// a map key which cannot be converted to a string. A map is serialized as JSON object,
    /// and JSON objects only support strings as member names.
    #[error("map key cannot be converted to string")]
    MapKeyNotString,
}

impl serde::ser::Error for SerializerError {
    fn custom<T: Display>(msg: T) -> Self {
        SerializerError::Custom(msg.to_string())
    }
}

/// Serde `Serializer` which delegates to a [`JsonWriter`]
///
/// Normally there is no need to directly use this serializer. Instead, the method
/// [`JsonWriter::serialize_value`] can be used.
///
/// # Examples
/// ```
/// # use struson::writer::*;
/// # use struson::serde::JsonWriterSerializer;
/// # use serde::*;
/// // In this example JSON bytes are stored in a Vec;
/// // normally they would be written to a file or network connection
/// let mut writer = Vec::<u8>::new();
/// let mut json_writer = JsonStreamWriter::new(&mut writer);
/// let mut serializer = JsonWriterSerializer::new(&mut json_writer);
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
/// value.serialize(&mut serializer)?;
///
/// // Ensures that the JSON document is complete and flushes the buffer
/// json_writer.finish_document()?;
///
/// assert_eq!(
///     r#"{"text":"some text","number":5}"#,
///     String::from_utf8(writer)?
/// );
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Error handling
/// A [`SerializerError`] is returned when the underlying `JsonWriter` or the
/// serializer itself encounters an error.
///
/// When one of the methods of this serializer return an error, serialization must be
/// aborted. Trying to call any serializer methods afterwards can lead to unspecified
/// behavior, such as errors, panics or incorrect data. However, no _undefined_ behavior
/// occurs.
///
/// # Panics
/// Methods of this serializer and of its associated types panic when used in an incorrect
/// way. The documentation of the methods describes in detail the situations when that will
/// happen. In general all these cases are related to incorrect usage by the user (such as
/// trying to serialize two map keys after each other without a value in between).
#[derive(Debug)]
pub struct JsonWriterSerializer<'a, W> {
    json_writer: &'a mut W,
}

impl<'a, W: JsonWriter> JsonWriterSerializer<'a, W> {
    /// Creates a serializer wrapping a [`JsonWriter`]
    ///
    /// The `JsonWriter` should be positioned to write the next value, for example it should
    /// not have written a top-level value yet or should be inside a JSON array. If this is
    /// not the case the serializer may panic during usage. See the `JsonWriter` documentation
    /// for more information when an error or panic can occur.
    pub fn new(json_writer: &'a mut W) -> Self {
        // TODO: Have to ensure that JsonWriter currently expects value?
        //   not sure if that is possible without exposing public function for JsonWriter
        JsonWriterSerializer { json_writer }
    }
}

fn map_number_err(e: JsonNumberError) -> SerializerError {
    match e {
        JsonNumberError::InvalidNumber(e) => SerializerError::InvalidNumber(e),
        JsonNumberError::IoError(e) => SerializerError::IoError(e),
    }
}

/* TODO: Move this documentation to the struct documentation? */
/// This implementation of [`Serializer`] tries to match Serde JSON's behavior, however there
/// might be some minor differences. Where relevant the documentation of the methods describes
/// how exactly a value is serialized to JSON.
///
/// If the exact behavior of Serde JSON is needed, the following workaround can be used, at the
/// cost of potentially worse performance:
/// ```
/// # use struson::reader::*;
/// # use struson::writer::*;
/// # use serde::Serialize;
/// #
/// # let mut writer = Vec::<u8>::new();
/// # let mut json_writer = JsonStreamWriter::new(&mut writer);
/// // Let's assume you already have a JsonWriter called `json_writer`
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
///
/// // 1. Serialize the value to a String with Serde JSON
/// let json = serde_json::to_string(&value)?;
/// // 2. Create a JsonStreamReader from the JSON
/// let mut json_reader = JsonStreamReader::new(json.as_bytes());
/// // 3. Transfer the JSON data to the original `json_writer`
/// json_reader.transfer_to(&mut json_writer)?;
/// // To be safe also call consume_trailing_whitespace()
/// json_reader.consume_trailing_whitespace()?;
///
/// // Continue using `json_writer` ...
/// # json_writer.finish_document()?;
/// # assert_eq!(
/// #     r#"{"text":"some text","number":5}"#,
/// #     String::from_utf8(writer)?
/// # );
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
/*
 * TODO: Guard direct access to wrapped JsonWriter; make sure document is complete and well formed
 *   Is creating invalid JSON actually possible? Apparently Serialize's API enforces that exactly one value is written, and that
 *   compound data such as structs are completed, due to return type of `Serialize::serialize`
 *   Though direct usage of JsonWriterSerializer might allow constructing incomplete values
 * TODO: In the documentation of the methods below use links when referring to other method,
 *   e.g. [`deserialize_map`]; however, rustdoc seems to be unable to create links?
 */
impl<'s, 'a, W: JsonWriter> Serializer for &'s mut JsonWriterSerializer<'a, W> {
    // No result type; data is written to JsonWriter
    type Ok = ();

    type Error = SerializerError;

    // Don't use Self here (and let JsonWriterSerializer implement all these traits) because it makes
    // usage of JsonWriterSerializer confusing and allows mixing calls to unrelated methods
    type SerializeSeq = SerializeSeq<'s, 'a, W>;
    type SerializeTuple = SerializeTuple<'s, 'a, W>;
    type SerializeTupleStruct = SerializeTupleStruct<'s, 'a, W>;
    type SerializeTupleVariant = SerializeTupleVariant<'s, 'a, W>;
    type SerializeMap = SerializeMap<'s, 'a, W>;
    type SerializeStruct = SerializeStruct<'s, 'a, W>;
    type SerializeStructVariant = SerializeStructVariant<'s, 'a, W>;

    fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error> {
        self.json_writer.bool_value(v)?;
        Ok(())
    }

    fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
        self.json_writer.number_value(v)?;
        Ok(())
    }

    fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
        self.json_writer.number_value(v)?;
        Ok(())
    }

    fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
        self.json_writer.number_value(v)?;
        Ok(())
    }

    fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
        self.json_writer.number_value(v)?;
        Ok(())
    }

    fn serialize_i128(self, v: i128) -> Result<Self::Ok, Self::Error> {
        self.json_writer.number_value(v)?;
        Ok(())
    }

    fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
        self.json_writer.number_value(v)?;
        Ok(())
    }

    fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
        self.json_writer.number_value(v)?;
        Ok(())
    }

    fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
        self.json_writer.number_value(v)?;
        Ok(())
    }

    fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
        self.json_writer.number_value(v)?;
        Ok(())
    }

    fn serialize_u128(self, v: u128) -> Result<Self::Ok, Self::Error> {
        self.json_writer.number_value(v)?;
        Ok(())
    }

    /// Serialize an `f32` value
    ///
    /// A [`SerializerError::InvalidNumber`] is returned if the value is non-finite, that is,
    /// if it is NaN or Infinity.
    fn serialize_f32(self, v: f32) -> Result<Self::Ok, Self::Error> {
        // Note: This differs from serde_json which maps NaN and Infinity to JSON null
        self.json_writer
            .fp_number_value(v)
            .map_err(map_number_err)?;
        Ok(())
    }

    /// Serialize an `f64` value
    ///
    /// A [`SerializerError::InvalidNumber`] is returned if the value is non-finite, that is,
    /// if it is NaN or Infinity.
    fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
        // Note: This differs from serde_json which maps NaN and Infinity to JSON null
        self.json_writer
            .fp_number_value(v)
            .map_err(map_number_err)?;
        Ok(())
    }

    /// Serialize a character
    ///
    /// This implementation writes a JSON string value containing only that
    /// single character (escaped if necessary).
    fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
        self.json_writer.string_value(&v.to_string())?;
        Ok(())
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        self.json_writer.string_value(v)?;
        Ok(())
    }

    /// Serialize a chunk of raw byte data
    ///
    /// This implementation serializes the data as JSON array containing the byte values
    /// as JSON numbers.
    fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
        // serde_json allows to customize this, see https://github.com/serde-rs/json/pull/1039
        // not sure if this can easily be supported here, and if this is worth it
        self.json_writer.begin_array()?;
        for b in v {
            self.json_writer.number_value(*b)?;
        }
        self.json_writer.end_array()?;
        Ok(())
    }

    /// Serialize a `None` value
    ///
    /// This implementation writes a JSON `null`.
    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        self.json_writer.null_value()?;
        Ok(())
    }

    /// Serialize a `Some(T)` value
    ///
    /// This implementation just serializes the provided value. Note that when the value is
    /// serialized as JSON `null` this can cause ambiguity for the JSON data because
    /// `serialize_none` also writes a JSON `null`.
    fn serialize_some<T: Serialize + ?Sized>(self, value: &T) -> Result<Self::Ok, Self::Error> {
        value.serialize(self)
    }

    /// Serialize a `()` value
    ///
    /// This implementation writes a JSON `null`.
    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        self.json_writer.null_value()?;
        Ok(())
    }

    /// Serialize a unit struct like `struct Unit`
    ///
    /// This implementation writes a JSON `null`, the given name is ignored.
    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        self.json_writer.null_value()?;
        Ok(())
    }

    /// Serialize a unit variant like `E::A` in `enum E { A, B }`
    ///
    /// This implementation writes the `variant` as JSON string value, the given name and
    /// variant index are ignored.
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        self.json_writer.string_value(variant)?;
        Ok(())
    }

    /// Serialize a newtype struct like `struct Millimeters(u8)`
    ///
    /// This implementation just serializes the provided value, the given name is ignored.
    fn serialize_newtype_struct<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error> {
        value.serialize(self)
    }

    /// Serialize a newtype variant like `E::N` in `enum E { N(u8) }`
    ///
    /// This implementation writes a JSON object consisting of a single member whose name
    /// is the `variant` and whose value is the serialized `value`. The given name and
    /// variant index are ignored.
    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error> {
        self.json_writer.begin_object()?;
        self.json_writer.name(variant)?;
        value.serialize(&mut *self)?;
        self.json_writer.end_object()?;
        Ok(())
    }

    /// Begin to serialize a variably sized sequence
    ///
    /// This implementation writes a JSON array, where each element written using
    /// [`SerializeSeq::serialize_element`](serde::ser::SerializeSeq::serialize_element)
    /// is serialized as array item. If `len` is `Some`, serializing a different number
    /// of elements than `len` will cause a [`SerializerError::IncorrectElementsCount`].
    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        self.json_writer.begin_array()?;
        Ok(SerializeSeq {
            ser: self,
            expected_len: len,
            len: 0,
        })
    }

    /// Begin to serialize a statically sized sequence
    ///
    /// This implementation writes a JSON array, where each element written using
    /// [`SerializeTuple::serialize_element`](serde::ser::SerializeTuple::serialize_element)
    /// is serialized as array item. Serializing a different number of elements than `len`
    /// will cause a [`SerializerError::IncorrectElementsCount`].
    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        self.json_writer.begin_array()?;
        Ok(SerializeTuple {
            ser: self,
            expected_len: len,
            len: 0,
        })
    }

    /// Begin to serialize a tuple struct like `struct Rgb(u8, u8, u8)`
    ///
    /// This implementation writes a JSON array, where each element written using
    /// [`SerializeTupleStruct::serialize_field`](serde::ser::SerializeTupleStruct::serialize_field)
    /// is serialized as array item. Serializing a different number of fields than `len`
    /// will cause a [`SerializerError::IncorrectElementsCount`]. The given name is ignored.
    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        self.json_writer.begin_array()?;
        Ok(SerializeTupleStruct {
            ser: self,
            expected_len: len,
            len: 0,
        })
    }

    /// Begin to serialize a tuple variant like `E::T` in `enum E { T(u8, u8) }`
    ///
    /// This implementation writes a JSON object consisting of a single member whose
    /// name is `variant` and whose value is a JSON array containing all fields serialized
    /// with [`SerializeTupleVariant::serialize_field`](serde::ser::SerializeTupleVariant::serialize_field).
    /// Serializing a different number of fields than `len` will cause a [`SerializerError::IncorrectElementsCount`].
    /// The given name and variant index are ignored.
    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        // Writes `{ variant: [`
        self.json_writer.begin_object()?;
        self.json_writer.name(variant)?;
        self.json_writer.begin_array()?;
        Ok(SerializeTupleVariant {
            ser: self,
            expected_len: len,
            len: 0,
        })
    }

    /// Begin to serialize a map
    ///
    /// This implementation writes a JSON object where each member consists of the
    /// key-value entry serialized using [`SerializeMap`](serde::ser::SerializeMap).
    ///
    /// Duplicate keys are not detected or prevented.
    ///
    /// # Errors
    /// If `len` is `Some`, serializing a different number of entries than `len` will
    /// cause a [`SerializerError::IncorrectElementsCount`].
    ///
    /// # Panics
    /// The same number of [`SerializeMap::serialize_key`](serde::ser::SerializeMap::serialize_key)
    /// and [`SerializeMap::serialize_value`](serde::ser::SerializeMap::serialize_value)
    /// calls have to be made and for every `serialize_key` call a `serialize_value` call
    /// has to follow, otherwise a panic will occur.
    /* TODO doc key conversion behavior? */
    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        self.json_writer.begin_object()?;
        Ok(SerializeMap {
            ser: self,
            expected_len: len,
            len: 0,
            // Initially entry key is expected
            expects_entry_value: false,
        })
    }

    /// Begin to serialize a struct like `struct Rgb { r: u8, g: u8, b: u8 }`
    ///
    /// This implementation writes a JSON object where each member consists of the
    /// field name and value serialized by [`SerializeStruct::serialize_field`](serde::ser::SerializeStruct::serialize_field).
    /// Serializing a different number of fields than `len` will cause a [`SerializerError::IncorrectElementsCount`].
    /// The given struct name is ignored.
    ///
    /// Duplicate field names are not detected or prevented.
    fn serialize_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        self.json_writer.begin_object()?;
        Ok(SerializeStruct {
            ser: self,
            expected_len: len,
            len: 0,
        })
    }

    /// Begin to serialize a struct variant like `E::S` in `enum E { S { r: u8, g: u8, b: u8 } }`
    ///
    /// This implementation writes a JSON object consisting of a single member whose
    /// name is `variant` and whose value is a nested JSON object where each member
    /// consists of the field name and value serialized by [`SerializeStructVariant::serialize_field`](serde::ser::SerializeStructVariant::serialize_field).
    ///
    /// Serializing a different number of fields than `len` will cause a [`SerializerError::IncorrectElementsCount`].
    /// The given struct name and variant index are ignored.
    ///
    /// Duplicate field names are not detected or prevented.
    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        // Writes `{ variant: {`
        self.json_writer.begin_object()?;
        self.json_writer.name(variant)?;
        self.json_writer.begin_object()?;
        Ok(SerializeStructVariant {
            ser: self,
            expected_len: len,
            len: 0,
        })
    }
}

#[doc(hidden)]
#[derive(Debug)]
pub struct SerializeSeq<'s, 'a, W: JsonWriter> {
    ser: &'s mut JsonWriterSerializer<'a, W>,
    expected_len: Option<usize>,
    len: usize,
}

impl<W: JsonWriter> serde::ser::SerializeSeq for SerializeSeq<'_, '_, W> {
    type Ok = ();
    type Error = SerializerError;

    fn serialize_element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        if let Some(expected_len) = self.expected_len {
            if self.len >= expected_len {
                return Err(SerializerError::IncorrectElementsCount {
                    expected: expected_len,
                    // + 1 for currently added element
                    actual: self.len + 1,
                });
            }
            self.len += 1;
        }
        value.serialize(&mut *self.ser)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        if let Some(expected_len) = self.expected_len {
            if self.len < expected_len {
                return Err(SerializerError::IncorrectElementsCount {
                    expected: expected_len,
                    actual: self.len,
                });
            }
        }
        self.ser.json_writer.end_array()?;
        Ok(())
    }
}

#[doc(hidden)]
#[derive(Debug)]
pub struct SerializeTuple<'s, 'a, W: JsonWriter> {
    ser: &'s mut JsonWriterSerializer<'a, W>,
    expected_len: usize,
    len: usize,
}

impl<W: JsonWriter> serde::ser::SerializeTuple for SerializeTuple<'_, '_, W> {
    type Ok = ();
    type Error = SerializerError;

    fn serialize_element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        if self.len >= self.expected_len {
            return Err(SerializerError::IncorrectElementsCount {
                expected: self.expected_len,
                // + 1 for currently added element
                actual: self.len + 1,
            });
        }
        self.len += 1;

        value.serialize(&mut *self.ser)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        if self.len < self.expected_len {
            return Err(SerializerError::IncorrectElementsCount {
                expected: self.expected_len,
                actual: self.len,
            });
        }
        self.ser.json_writer.end_array()?;
        Ok(())
    }
}

#[doc(hidden)]
#[derive(Debug)]
pub struct SerializeTupleStruct<'s, 'a, W: JsonWriter> {
    ser: &'s mut JsonWriterSerializer<'a, W>,
    expected_len: usize,
    len: usize,
}

impl<W: JsonWriter> serde::ser::SerializeTupleStruct for SerializeTupleStruct<'_, '_, W> {
    type Ok = ();
    type Error = SerializerError;

    fn serialize_field<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        if self.len >= self.expected_len {
            return Err(SerializerError::IncorrectElementsCount {
                expected: self.expected_len,
                // + 1 for currently added field
                actual: self.len + 1,
            });
        }
        self.len += 1;

        value.serialize(&mut *self.ser)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        if self.len < self.expected_len {
            return Err(SerializerError::IncorrectElementsCount {
                expected: self.expected_len,
                actual: self.len,
            });
        }
        self.ser.json_writer.end_array()?;
        Ok(())
    }
}

#[doc(hidden)]
#[derive(Debug)]
pub struct SerializeTupleVariant<'s, 'a, W: JsonWriter> {
    ser: &'s mut JsonWriterSerializer<'a, W>,
    expected_len: usize,
    len: usize,
}

impl<W: JsonWriter> serde::ser::SerializeTupleVariant for SerializeTupleVariant<'_, '_, W> {
    type Ok = ();
    type Error = SerializerError;

    fn serialize_field<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        if self.len >= self.expected_len {
            return Err(SerializerError::IncorrectElementsCount {
                expected: self.expected_len,
                // + 1 for currently added field
                actual: self.len + 1,
            });
        }
        self.len += 1;

        value.serialize(&mut *self.ser)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        if self.len < self.expected_len {
            return Err(SerializerError::IncorrectElementsCount {
                expected: self.expected_len,
                actual: self.len,
            });
        }

        // Matches serialize_tuple_variant
        self.ser.json_writer.end_array()?;
        self.ser.json_writer.end_object()?;
        Ok(())
    }
}

#[doc(hidden)]
#[derive(Debug)]
pub struct SerializeMap<'s, 'a, W: JsonWriter> {
    ser: &'s mut JsonWriterSerializer<'a, W>,
    expected_len: Option<usize>,
    len: usize,
    expects_entry_value: bool,
}

impl<W: JsonWriter> serde::ser::SerializeMap for SerializeMap<'_, '_, W> {
    type Ok = ();
    type Error = SerializerError;

    fn serialize_key<T: Serialize + ?Sized>(&mut self, key: &T) -> Result<(), Self::Error> {
        if self.expects_entry_value {
            panic!("Incorrect usage: Cannot serialize key when value is expected")
        }

        if let Some(expected_len) = self.expected_len {
            if self.len >= expected_len {
                return Err(SerializerError::IncorrectElementsCount {
                    expected: expected_len,
                    // + 1 for currently added entry
                    actual: self.len + 1,
                });
            }
            self.len += 1;
        }
        self.expects_entry_value = true;
        key.serialize(&mut MapKeyStringSerializer {
            json_writer: self.ser.json_writer,
        })
    }

    fn serialize_value<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        if !self.expects_entry_value {
            panic!("Incorrect usage: Cannot serialize value when key is expected")
        }
        self.expects_entry_value = false;
        value.serialize(&mut *self.ser)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        if self.expects_entry_value {
            panic!("Incorrect usage: Cannot end map when value is expected")
        }

        if let Some(expected_len) = self.expected_len {
            if self.len < expected_len {
                return Err(SerializerError::IncorrectElementsCount {
                    expected: expected_len,
                    actual: self.len,
                });
            }
        }
        self.ser.json_writer.end_object()?;
        Ok(())
    }
}

#[doc(hidden)]
#[derive(Debug)]
pub struct SerializeStruct<'s, 'a, W: JsonWriter> {
    ser: &'s mut JsonWriterSerializer<'a, W>,
    expected_len: usize,
    len: usize,
}

impl<W: JsonWriter> serde::ser::SerializeStruct for SerializeStruct<'_, '_, W> {
    type Ok = ();
    type Error = SerializerError;

    fn serialize_field<T: Serialize + ?Sized>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Self::Error> {
        if self.len >= self.expected_len {
            return Err(SerializerError::IncorrectElementsCount {
                expected: self.expected_len,
                // + 1 for currently added field
                actual: self.len + 1,
            });
        }
        self.len += 1;

        self.ser.json_writer.name(key)?;
        value.serialize(&mut *self.ser)
    }

    fn skip_field(&mut self, _key: &'static str) -> Result<(), Self::Error> {
        if self.len >= self.expected_len {
            return Err(SerializerError::IncorrectElementsCount {
                expected: self.expected_len,
                // + 1 for currently added field
                actual: self.len + 1,
            });
        }
        self.len += 1;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        if self.len < self.expected_len {
            return Err(SerializerError::IncorrectElementsCount {
                expected: self.expected_len,
                actual: self.len,
            });
        }
        self.ser.json_writer.end_object()?;
        Ok(())
    }
}

#[doc(hidden)]
#[derive(Debug)]
pub struct SerializeStructVariant<'s, 'a, W: JsonWriter> {
    ser: &'s mut JsonWriterSerializer<'a, W>,
    expected_len: usize,
    len: usize,
}

impl<W: JsonWriter> serde::ser::SerializeStructVariant for SerializeStructVariant<'_, '_, W> {
    type Ok = ();
    type Error = SerializerError;

    fn serialize_field<T: Serialize + ?Sized>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Self::Error> {
        if self.len >= self.expected_len {
            return Err(SerializerError::IncorrectElementsCount {
                expected: self.expected_len,
                // + 1 for currently added field
                actual: self.len + 1,
            });
        }
        self.len += 1;

        self.ser.json_writer.name(key)?;
        value.serialize(&mut *self.ser)
    }

    fn skip_field(&mut self, _key: &'static str) -> Result<(), Self::Error> {
        if self.len >= self.expected_len {
            return Err(SerializerError::IncorrectElementsCount {
                expected: self.expected_len,
                // + 1 for currently added field
                actual: self.len + 1,
            });
        }
        self.len += 1;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        if self.len < self.expected_len {
            return Err(SerializerError::IncorrectElementsCount {
                expected: self.expected_len,
                actual: self.len,
            });
        }

        // Matches serialize_struct_variant
        self.ser.json_writer.end_object()?;
        self.ser.json_writer.end_object()?;
        Ok(())
    }
}

/// Serializer for serializing a map key as string
///
/// Tries to match serde_json's internal [`MapKeySerializer`](https://github.com/serde-rs/json/blob/v1.0.107/src/ser.rs#L791)
/// behavior.
#[derive(Debug)]
struct MapKeyStringSerializer<'a, W: JsonWriter> {
    json_writer: &'a mut W,
}

impl<W: JsonWriter> MapKeyStringSerializer<'_, W> {
    fn serialize_finite_number_key<N: FiniteNumber>(
        &mut self,
        number: N,
    ) -> Result<(), SerializerError> {
        // For consistency use same number serialization logic as JsonWriter
        number
            .use_json_number(|s| self.json_writer.name(s))
            .map_err(SerializerError::IoError)
    }

    fn serialize_fp_number_key<N: FloatingPointNumber>(
        &mut self,
        number: N,
    ) -> Result<(), SerializerError> {
        // For consistency use same number serialization logic as JsonWriter
        number
            .use_json_number(|s| self.json_writer.name(s))
            .map_err(map_number_err)
    }
}

fn err_key_not_string<T>() -> Result<T, SerializerError> {
    Err(SerializerError::MapKeyNotString)
}

impl<W: JsonWriter> Serializer for &mut MapKeyStringSerializer<'_, W> {
    type Ok = ();
    type Error = SerializerError;
    type SerializeSeq = Impossible<(), Self::Error>;
    type SerializeTuple = Impossible<(), Self::Error>;
    type SerializeTupleStruct = Impossible<(), Self::Error>;
    type SerializeTupleVariant = Impossible<(), Self::Error>;
    type SerializeMap = Impossible<(), Self::Error>;
    type SerializeStruct = Impossible<(), Self::Error>;
    type SerializeStructVariant = Impossible<(), Self::Error>;

    fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error> {
        self.serialize_str(if v { "true" } else { "false" })
    }

    fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
        self.serialize_finite_number_key(v)
    }

    fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
        self.serialize_finite_number_key(v)
    }

    fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
        self.serialize_finite_number_key(v)
    }

    fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
        self.serialize_finite_number_key(v)
    }

    fn serialize_i128(self, v: i128) -> Result<Self::Ok, Self::Error> {
        self.serialize_finite_number_key(v)
    }

    fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
        self.serialize_finite_number_key(v)
    }

    fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
        self.serialize_finite_number_key(v)
    }

    fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
        self.serialize_finite_number_key(v)
    }

    fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
        self.serialize_finite_number_key(v)
    }

    fn serialize_u128(self, v: u128) -> Result<Self::Ok, Self::Error> {
        self.serialize_finite_number_key(v)
    }

    fn serialize_f32(self, v: f32) -> Result<Self::Ok, Self::Error> {
        self.serialize_fp_number_key(v)
    }

    fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
        self.serialize_fp_number_key(v)
    }

    fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
        self.serialize_str(&v.to_string())
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        self.json_writer.name(v)?;
        Ok(())
    }

    fn serialize_some<T: Serialize + ?Sized>(self, value: &T) -> Result<Self::Ok, Self::Error> {
        value.serialize(self)
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        self.serialize_str(variant)
    }

    fn serialize_newtype_struct<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error> {
        value.serialize(self)
    }

    /* The following types are not supported as key */

    fn serialize_bytes(self, _v: &[u8]) -> Result<Self::Ok, Self::Error> {
        err_key_not_string()
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        err_key_not_string()
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        err_key_not_string()
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        err_key_not_string()
    }

    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _value: &T,
    ) -> Result<Self::Ok, Self::Error> {
        err_key_not_string()
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        err_key_not_string()
    }

    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        err_key_not_string()
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        err_key_not_string()
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        err_key_not_string()
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        err_key_not_string()
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        err_key_not_string()
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        err_key_not_string()
    }
}

#[cfg(test)]
mod tests {
    use std::vec;

    use serde::{
        ser::{
            SerializeMap, SerializeSeq, SerializeStruct, SerializeStructVariant, SerializeTuple,
            SerializeTupleStruct, SerializeTupleVariant,
        },
        Serialize, Serializer,
    };

    use super::{JsonWriterSerializer, SerializerError};
    use crate::writer::{JsonStreamWriter, JsonWriter};

    fn assert_serialized<
        F: Fn(
            &mut JsonWriterSerializer<JsonStreamWriter<&mut Vec<u8>>>,
        ) -> Result<(), SerializerError>,
    >(
        serializing_function: F,
        expected_json: &str,
    ) {
        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        let mut serializer = JsonWriterSerializer::new(&mut json_writer);
        serializing_function(&mut serializer).unwrap();
        json_writer.finish_document().unwrap();
        assert_eq!(
            expected_json,
            String::from_utf8(writer).unwrap(),
            "expected JSON does not match Struson output"
        );
    }

    fn assert_serialized_serde_json<
        F: Fn(&mut serde_json::Serializer<&mut Vec<u8>>) -> Result<(), serde_json::Error>,
    >(
        serializing_function: F,
        expected_json: &str,
    ) {
        let mut writer = Vec::<u8>::new();
        let mut serializer = serde_json::Serializer::new(&mut writer);
        serializing_function(&mut serializer).unwrap();
        assert_eq!(
            expected_json,
            String::from_utf8(writer).unwrap(),
            "expected JSON does not match serde_json output"
        );
    }

    /// Asserts that both the serialized JSON from this module as well as serde_json's JSON
    /// match the expected JSON
    macro_rules! assert_serialized_cmp {
        // This syntax emulates a closure: |s| { ... }
        (|$serializer:ident| $serializing_function_body:block, $expected_json:expr) => {
            assert_serialized(|$serializer| $serializing_function_body, $expected_json);

            {
                // For serde_json this workaround is needed because directly using serde_json::Serializer seems to
                // cause "multiple applicable items in scope" error due to serde_json's internal Compound struct
                // which implements multiple of the ...Access traits, which have conflicting methods
                struct S;
                impl Serialize for S {
                    fn serialize<S: Serializer>(&self, $serializer: S) -> Result<S::Ok, S::Error> {
                        $serializing_function_body
                    }
                }
                let mut writer = Vec::<u8>::new();
                let mut serializer = serde_json::Serializer::new(&mut writer);
                S.serialize(&mut serializer).unwrap();
                assert_eq!(
                    $expected_json,
                    String::from_utf8(writer).unwrap(),
                    "expected JSON does not match serde_json output"
                );
            }
        };
        // Simple form for cases where serde_json's Compound struct is not causing ambiguities
        ($serializing_function:expr, $expected_json:expr) => {
            assert_serialized($serializing_function, $expected_json);
            assert_serialized_serde_json($serializing_function, $expected_json);
        }
    }

    fn assert_number_error<
        F: Fn(
            &mut JsonWriterSerializer<JsonStreamWriter<std::io::Sink>>,
        ) -> Result<(), SerializerError>,
    >(
        serializing_function: F,
        expected_error_message: &str,
    ) {
        let mut json_writer = JsonStreamWriter::new(std::io::sink());
        let mut serializer = JsonWriterSerializer::new(&mut json_writer);
        match serializing_function(&mut serializer) {
            Ok(_) => panic!("Should have failed with error message: {expected_error_message}"),
            Err(e) => match e {
                SerializerError::InvalidNumber(message) => {
                    assert_eq!(expected_error_message, message)
                }
                _ => panic!("Unexpected error: {e:?}"),
            },
        }
    }

    /// Asserts that serializing too few (`F1`) or too many (`F2`) elements causes an error
    ///
    /// - `F1` should claim to serialize 1 element but try to call `end()` without having written
    ///   anything yet.
    /// - `F2` should claim to serialize 0 elements but actually try to serialize an element.
    fn assert_elements_count_error<
        F1: Fn(
            &mut JsonWriterSerializer<JsonStreamWriter<std::io::Sink>>,
        ) -> Result<(), SerializerError>,
        F2: Fn(
            &mut JsonWriterSerializer<JsonStreamWriter<std::io::Sink>>,
        ) -> Result<(), SerializerError>,
    >(
        serialize_none: F1,
        serialize_one: F2,
    ) {
        fn assert_result<
            F: Fn(
                &mut JsonWriterSerializer<JsonStreamWriter<std::io::Sink>>,
            ) -> Result<(), SerializerError>,
        >(
            serializing_function: F,
            expected_expected: usize,
            expected_actual: usize,
        ) {
            let mut json_writer = JsonStreamWriter::new(std::io::sink());
            let mut serializer = JsonWriterSerializer::new(&mut json_writer);
            match serializing_function(&mut serializer) {
                Ok(_) => panic!("Should have failed with error"),
                Err(e) => match e {
                    SerializerError::IncorrectElementsCount { expected, actual } => {
                        assert_eq!(expected_expected, expected);
                        assert_eq!(expected_actual, actual);
                    }
                    _ => panic!("Unexpected error: {e:?}"),
                },
            }
        }

        assert_result(serialize_none, 1, 0);
        assert_result(serialize_one, 0, 1);
    }

    #[test]
    fn serialize_bool() {
        assert_serialized_cmp!(|s| s.serialize_bool(true), "true");

        assert_serialized_cmp!(|s| s.serialize_bool(false), "false");
    }

    #[test]
    fn serialize_bytes() {
        assert_serialized_cmp!(|s| s.serialize_bytes(&[]), "[]");

        assert_serialized_cmp!(|s| s.serialize_bytes(&[0, 127, 255]), "[0,127,255]");
    }

    #[test]
    fn serialize_char() {
        assert_serialized_cmp!(|s| s.serialize_char('a'), "\"a\"");

        assert_serialized_cmp!(|s| s.serialize_char('\0'), "\"\\u0000\"");

        assert_serialized_cmp!(|s| s.serialize_char('\u{10FFFF}'), "\"\u{10FFFF}\"");
    }

    #[test]
    fn serialize_f32() {
        assert_serialized(|s| s.serialize_f32(0.0), "0");

        assert_serialized(|s| s.serialize_f32(-0.0), "-0");

        assert_serialized_cmp!(|s| s.serialize_f32(123.45), "123.45");

        assert_number_error(
            |s| s.serialize_f32(f32::NAN),
            &format!("non-finite number: {}", f32::NAN),
        );
        assert_number_error(
            |s| s.serialize_f32(f32::INFINITY),
            &format!("non-finite number: {}", f32::INFINITY),
        );
    }

    #[test]
    fn serialize_f64() {
        assert_serialized(|s| s.serialize_f64(0.0), "0");

        assert_serialized(|s| s.serialize_f64(-0.0), "-0");

        assert_serialized_cmp!(|s| s.serialize_f64(123.45), "123.45");

        assert_number_error(
            |s| s.serialize_f64(f64::NAN),
            &format!("non-finite number: {}", f64::NAN),
        );
        assert_number_error(
            |s| s.serialize_f64(f64::INFINITY),
            &format!("non-finite number: {}", f64::INFINITY),
        );
    }

    #[test]
    fn serialize_i8() {
        assert_serialized_cmp!(|s| s.serialize_i8(-3), "-3");
        assert_serialized_cmp!(|s| s.serialize_i8(3), "3");

        assert_serialized_cmp!(|s| s.serialize_i8(i8::MIN), "-128");
        assert_serialized_cmp!(|s| s.serialize_i8(i8::MAX), "127");
    }

    #[test]
    fn serialize_i16() {
        assert_serialized_cmp!(|s| s.serialize_i16(-3), "-3");
        assert_serialized_cmp!(|s| s.serialize_i16(3), "3");

        assert_serialized_cmp!(|s| s.serialize_i16(i16::MIN), "-32768");
        assert_serialized_cmp!(|s| s.serialize_i16(i16::MAX), "32767");
    }

    #[test]
    fn serialize_i32() {
        assert_serialized_cmp!(|s| s.serialize_i32(-3), "-3");
        assert_serialized_cmp!(|s| s.serialize_i32(3), "3");

        assert_serialized_cmp!(|s| s.serialize_i32(i32::MIN), "-2147483648");
        assert_serialized_cmp!(|s| s.serialize_i32(i32::MAX), "2147483647");
    }

    #[test]
    fn serialize_i64() {
        assert_serialized_cmp!(|s| s.serialize_i64(-3), "-3");
        assert_serialized_cmp!(|s| s.serialize_i64(3), "3");

        assert_serialized_cmp!(|s| s.serialize_i64(i64::MIN), "-9223372036854775808");
        assert_serialized_cmp!(|s| s.serialize_i64(i64::MAX), "9223372036854775807");
    }

    #[test]
    fn serialize_i128() {
        assert_serialized_cmp!(|s| s.serialize_i128(-3), "-3");
        assert_serialized_cmp!(|s| s.serialize_i128(3), "3");

        assert_serialized_cmp!(
            |s| s.serialize_i128(i128::MIN),
            "-170141183460469231731687303715884105728"
        );
        assert_serialized_cmp!(
            |s| s.serialize_i128(i128::MAX),
            "170141183460469231731687303715884105727"
        );
    }

    #[test]
    fn serialize_u8() {
        assert_serialized_cmp!(|s| s.serialize_u8(3), "3");
        assert_serialized_cmp!(|s| s.serialize_u8(u8::MAX), "255");
    }

    #[test]
    fn serialize_u16() {
        assert_serialized_cmp!(|s| s.serialize_u16(3), "3");
        assert_serialized_cmp!(|s| s.serialize_u16(u16::MAX), "65535");
    }

    #[test]
    fn serialize_u32() {
        assert_serialized_cmp!(|s| s.serialize_u32(3), "3");
        assert_serialized_cmp!(|s| s.serialize_u32(u32::MAX), "4294967295");
    }

    #[test]
    fn serialize_u64() {
        assert_serialized_cmp!(|s| s.serialize_u64(3), "3");
        assert_serialized_cmp!(|s| s.serialize_u64(u64::MAX), "18446744073709551615");
    }

    #[test]
    fn serialize_u128() {
        assert_serialized_cmp!(|s| s.serialize_u128(3), "3");
        assert_serialized_cmp!(
            |s| s.serialize_u128(u128::MAX),
            "340282366920938463463374607431768211455"
        );
    }

    mod serialize_map {
        use super::*;

        #[test]
        fn serialize() {
            assert_serialized_cmp!(
                |s| {
                    let map = s.serialize_map(None)?;
                    map.end()
                },
                "{}"
            );

            assert_serialized_cmp!(
                |s| {
                    let mut map = s.serialize_map(None)?;
                    map.serialize_key("a")?;
                    map.serialize_value(&1)?;
                    map.end()
                },
                r#"{"a":1}"#
            );

            assert_serialized_cmp!(
                |s| {
                    // Provide size hint
                    let mut map = s.serialize_map(Some(1))?;
                    map.serialize_key("a")?;
                    map.serialize_value(&1)?;
                    map.end()
                },
                r#"{"a":1}"#
            );

            assert_serialized_cmp!(
                |s| {
                    let mut map = s.serialize_map(None)?;
                    map.serialize_key("a")?;
                    map.serialize_value(&1)?;

                    // Duplicate key
                    map.serialize_key("a")?;
                    map.serialize_value(&2)?;
                    map.end()
                },
                r#"{"a":1,"a":2}"#
            );

            assert_serialized_cmp!(
                |s| {
                    let mut map = s.serialize_map(None)?;
                    map.serialize_key("a")?;

                    struct NestedMap;
                    impl Serialize for NestedMap {
                        fn serialize<S: Serializer>(
                            &self,
                            serializer: S,
                        ) -> Result<S::Ok, S::Error> {
                            // Nested map
                            let mut map = serializer.serialize_map(None)?;
                            map.serialize_key("b")?;
                            map.serialize_value(&1)?;
                            map.end()
                        }
                    }
                    map.serialize_value(&NestedMap)?;

                    map.end()
                },
                r#"{"a":{"b":1}}"#
            );

            assert_elements_count_error(
                |s| {
                    let map = s.serialize_map(Some(1))?;
                    map.end()
                },
                |s| {
                    let mut map = s.serialize_map(Some(0))?;
                    map.serialize_key("a")
                },
            );
        }

        #[test]
        fn string_key_conversion() {
            assert_serialized_cmp!(
                |s| {
                    let mut map = s.serialize_map(None)?;

                    map.serialize_key(&true)?;
                    map.serialize_value(&0)?;

                    map.serialize_key(&false)?;
                    map.serialize_value(&0)?;

                    map.serialize_key(&2_u8)?;
                    map.serialize_value(&0)?;

                    map.serialize_key(&3_i128)?;
                    map.serialize_value(&0)?;

                    map.serialize_key(&1.23_f32)?;
                    map.serialize_value(&0)?;

                    map.serialize_key(&'a')?;
                    map.serialize_value(&0)?;

                    map.serialize_key(&Some("value"))?;
                    map.serialize_value(&0)?;

                    struct UnitVariant;
                    impl Serialize for UnitVariant {
                        fn serialize<S: Serializer>(
                            &self,
                            serializer: S,
                        ) -> Result<S::Ok, S::Error> {
                            serializer.serialize_unit_variant("name", 1, "UnitVariant")
                        }
                    }

                    map.serialize_key(&UnitVariant)?;
                    map.serialize_value(&0)?;

                    struct NewtypeStruct;
                    impl Serialize for NewtypeStruct {
                        fn serialize<S: Serializer>(
                            &self,
                            serializer: S,
                        ) -> Result<S::Ok, S::Error> {
                            serializer.serialize_newtype_struct("name", "NewtypeStruct")
                        }
                    }

                    map.serialize_key(&NewtypeStruct)?;
                    map.serialize_value(&0)?;

                    map.end()
                },
                r#"{"true":0,"false":0,"2":0,"3":0,"1.23":0,"a":0,"value":0,"UnitVariant":0,"NewtypeStruct":0}"#
            );
        }

        #[test]
        fn string_key_error() {
            macro_rules! assert_map_key_error {
                ($key:expr, $err_pattern:pat_param => $err_assertion:expr) => {
                    {
                        let mut json_writer = JsonStreamWriter::new(std::io::sink());
                        let mut serializer = JsonWriterSerializer::new(&mut json_writer);
                        let mut map = serializer.serialize_map(None).unwrap();
                        match map.serialize_key(&$key) {
                            Ok(_) => panic!("Should have failed for Struson"),
                            Err(e) => match e {
                                $err_pattern => $err_assertion,
                                _ => panic!("Unexpected error for Struson: {e:?}"),
                            },
                        }
                    }
                    {
                        let mut serializer = serde_json::Serializer::new(std::io::sink());
                        let mut map = serializer.serialize_map(None).unwrap();
                        match map.serialize_key(&$key) {
                            Ok(_) => panic!("Should have failed for serde_json"),
                            // Don't check exact serde_json error message
                            Err(_) => {},
                        }
                    }
                };
                ($key:expr, $err_pattern:pat_param) => {
                    assert_map_key_error!($key, $err_pattern => {});
                };
            }

            assert_map_key_error!(
                f32::NAN,
                SerializerError::InvalidNumber(message) => assert_eq!(format!("non-finite number: {}", f32::NAN), message)
            );
            assert_map_key_error!(
                f64::INFINITY,
                SerializerError::InvalidNumber(message) => assert_eq!(format!("non-finite number: {}", f64::INFINITY), message)
            );

            assert_map_key_error!([1_u8], SerializerError::MapKeyNotString);

            assert_map_key_error!(vec!["a"], SerializerError::MapKeyNotString);

            struct NewtypeStruct<N: Serialize>(N);
            impl<N: Serialize> Serialize for NewtypeStruct<N> {
                fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                    serializer.serialize_newtype_struct("name", &self.0)
                }
            }

            assert_map_key_error!(NewtypeStruct(vec!["a"]), SerializerError::MapKeyNotString);
        }

        fn use_map_serializer<
            F: Fn(
                crate::serde::ser::SerializeMap<'_, '_, JsonStreamWriter<std::io::Sink>>,
            ) -> Result<(), SerializerError>,
        >(
            serializing_function: F,
        ) {
            let mut json_writer = JsonStreamWriter::new(std::io::sink());
            let mut serializer = JsonWriterSerializer::new(&mut json_writer);
            let map = serializer.serialize_map(None).unwrap();
            serializing_function(map).unwrap();
        }

        #[test]
        #[should_panic(expected = "Incorrect usage: Cannot serialize value when key is expected")]
        fn unexpected_value() {
            use_map_serializer(|mut map| map.serialize_value(&1));
        }

        #[test]
        #[should_panic(expected = "Incorrect usage: Cannot serialize key when value is expected")]
        fn unexpected_key() {
            use_map_serializer(|mut map| {
                map.serialize_key("a")?;
                map.serialize_key("b")
            });
        }

        #[test]
        #[should_panic(expected = "Incorrect usage: Cannot end map when value is expected")]
        fn end_missing_value() {
            use_map_serializer(|mut map| {
                map.serialize_key("a")?;
                map.end()
            });
        }
    }

    #[test]
    fn serialize_newtype_struct() {
        assert_serialized_cmp!(
            |s| s.serialize_newtype_struct("name", &"value"),
            "\"value\""
        );
    }

    #[test]
    fn serialize_newtype_variant() {
        assert_serialized_cmp!(
            |s| s.serialize_newtype_variant("name", 1, "variant", &"value"),
            r#"{"variant":"value"}"#
        );
    }

    #[test]
    fn serialize_none() {
        assert_serialized_cmp!(|s| s.serialize_none(), "null");
    }

    #[test]
    fn serialize_some() {
        assert_serialized_cmp!(|s| s.serialize_some("value"), "\"value\"");
    }

    #[test]
    fn serialize_seq() {
        assert_serialized_cmp!(
            |s| {
                let seq = s.serialize_seq(None)?;
                seq.end()
            },
            "[]"
        );

        assert_serialized_cmp!(
            |s| {
                let mut seq = s.serialize_seq(None)?;
                seq.serialize_element(&1)?;
                seq.end()
            },
            "[1]"
        );

        assert_serialized_cmp!(
            |s| {
                // Provide size hint
                let mut seq = s.serialize_seq(Some(1))?;
                seq.serialize_element(&1)?;
                seq.end()
            },
            "[1]"
        );

        assert_serialized_cmp!(
            |s| {
                let mut seq = s.serialize_seq(None)?;
                seq.serialize_element(&1)?;
                seq.serialize_element(&2)?;
                seq.end()
            },
            "[1,2]"
        );

        assert_serialized_cmp!(
            |s| {
                let mut seq = s.serialize_seq(None)?;

                struct NestedSeq;
                impl Serialize for NestedSeq {
                    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                        let mut seq = serializer.serialize_seq(None)?;
                        seq.serialize_element(&1)?;
                        seq.serialize_element(&2)?;
                        seq.end()
                    }
                }
                seq.serialize_element(&NestedSeq)?;

                seq.end()
            },
            "[[1,2]]"
        );

        assert_elements_count_error(
            |s| {
                let seq = s.serialize_seq(Some(1))?;
                seq.end()
            },
            |s| {
                let mut seq = s.serialize_seq(Some(0))?;
                seq.serialize_element(&1)
            },
        );
    }

    #[test]
    fn serialize_str() {
        assert_serialized_cmp!(|s| s.serialize_str(""), "\"\"");

        assert_serialized_cmp!(|s| s.serialize_str("test"), "\"test\"");

        assert_serialized_cmp!(|s| s.serialize_str("\0"), "\"\\u0000\"");

        assert_serialized_cmp!(|s| s.serialize_str("\u{10FFFF}"), "\"\u{10FFFF}\"");
    }

    #[test]
    fn serialize_struct() {
        assert_serialized_cmp!(
            |s| {
                let struc = s.serialize_struct("name", 0)?;
                struc.end()
            },
            "{}"
        );

        assert_serialized_cmp!(
            |s| {
                let mut struc = s.serialize_struct("name", 1)?;
                struc.serialize_field("key", &1)?;
                struc.end()
            },
            r#"{"key":1}"#
        );

        assert_serialized_cmp!(
            |s| {
                let mut struc = s.serialize_struct("name", 3)?;
                struc.serialize_field("key1", &1)?;
                struc.skip_field("skipped")?;
                struc.serialize_field("key2", &2)?;
                struc.end()
            },
            r#"{"key1":1,"key2":2}"#
        );

        assert_elements_count_error(
            |s| {
                let struc = s.serialize_struct("name", 1)?;
                struc.end()
            },
            |s| {
                let mut struc = s.serialize_struct("name", 0)?;
                struc.serialize_field("key1", &1)
            },
        );
    }

    #[test]
    fn serialize_struct_variant() {
        assert_serialized_cmp!(
            |s| {
                let struc = s.serialize_struct_variant("name", 1, "variant", 0)?;
                struc.end()
            },
            r#"{"variant":{}}"#
        );

        assert_serialized_cmp!(
            |s| {
                let mut struc = s.serialize_struct_variant("name", 1, "variant", 1)?;
                struc.serialize_field("key", &1)?;
                struc.end()
            },
            r#"{"variant":{"key":1}}"#
        );

        assert_serialized_cmp!(
            |s| {
                let mut struc = s.serialize_struct_variant("name", 1, "variant", 3)?;
                struc.serialize_field("key1", &1)?;
                struc.skip_field("skipped")?;
                struc.serialize_field("key2", &2)?;
                struc.end()
            },
            r#"{"variant":{"key1":1,"key2":2}}"#
        );

        assert_elements_count_error(
            |s| {
                let struc = s.serialize_struct_variant("name", 1, "variant", 1)?;
                struc.end()
            },
            |s| {
                let mut struc = s.serialize_struct_variant("name", 1, "variant", 0)?;
                struc.serialize_field("key1", &1)
            },
        );
    }

    #[test]
    fn serialize_tuple() {
        assert_serialized_cmp!(
            |s| {
                let tuple = s.serialize_tuple(0)?;
                tuple.end()
            },
            "[]"
        );

        assert_serialized_cmp!(
            |s| {
                let mut tuple = s.serialize_tuple(1)?;
                tuple.serialize_element(&1)?;
                tuple.end()
            },
            "[1]"
        );

        assert_serialized_cmp!(
            |s| {
                let mut tuple = s.serialize_tuple(2)?;
                tuple.serialize_element(&1)?;
                tuple.serialize_element(&2)?;
                tuple.end()
            },
            "[1,2]"
        );

        assert_elements_count_error(
            |s| {
                let tuple = s.serialize_tuple(1)?;
                tuple.end()
            },
            |s| {
                let mut tuple = s.serialize_tuple(0)?;
                tuple.serialize_element(&1)
            },
        );
    }

    #[test]
    fn serialize_tuple_struct() {
        assert_serialized_cmp!(
            |s| {
                let tuple = s.serialize_tuple_struct("name", 0)?;
                tuple.end()
            },
            "[]"
        );

        assert_serialized_cmp!(
            |s| {
                let mut tuple = s.serialize_tuple_struct("name", 1)?;
                tuple.serialize_field(&1)?;
                tuple.end()
            },
            "[1]"
        );

        assert_serialized_cmp!(
            |s| {
                let mut tuple = s.serialize_tuple_struct("name", 2)?;
                tuple.serialize_field(&1)?;
                tuple.serialize_field(&2)?;
                tuple.end()
            },
            "[1,2]"
        );

        assert_elements_count_error(
            |s| {
                let tuple = s.serialize_tuple(1)?;
                tuple.end()
            },
            |s| {
                let mut tuple = s.serialize_tuple(0)?;
                tuple.serialize_element(&1)
            },
        );
    }

    #[test]
    fn serialize_tuple_variant() {
        assert_serialized_cmp!(
            |s| {
                let tuple = s.serialize_tuple_variant("name", 0, "variant", 0)?;
                tuple.end()
            },
            r#"{"variant":[]}"#
        );

        assert_serialized_cmp!(
            |s| {
                let mut tuple = s.serialize_tuple_variant("name", 0, "variant", 1)?;
                tuple.serialize_field(&1)?;
                tuple.end()
            },
            r#"{"variant":[1]}"#
        );

        assert_serialized_cmp!(
            |s| {
                let mut tuple = s.serialize_tuple_variant("name", 0, "variant", 2)?;
                tuple.serialize_field(&1)?;
                tuple.serialize_field(&2)?;
                tuple.end()
            },
            r#"{"variant":[1,2]}"#
        );

        assert_elements_count_error(
            |s| {
                let tuple = s.serialize_tuple_variant("name", 0, "variant", 1)?;
                tuple.end()
            },
            |s| {
                let mut tuple = s.serialize_tuple_variant("name", 0, "variant", 0)?;
                tuple.serialize_field(&1)
            },
        );
    }

    #[test]
    fn serialize_unit() {
        assert_serialized_cmp!(|s| s.serialize_unit(), "null");
    }

    #[test]
    fn serialize_unit_struct() {
        assert_serialized_cmp!(|s| s.serialize_unit_struct("name"), "null");
    }

    #[test]
    fn serialize_unit_variant() {
        assert_serialized_cmp!(
            |s| s.serialize_unit_variant("name", 0, "variant"),
            "\"variant\""
        );
    }
}
