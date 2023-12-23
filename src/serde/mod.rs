//! Provides integration with [Serde](https://docs.rs/serde/latest/serde/)
//!
//! This module provides optional integration with Serde by allowing [`Serialize`](serde::ser::Serialize)
//! types to be written to a [`JsonWriter`](crate::writer::JsonWriter) and [`Deserialize`](serde::de::Deserialize)
//! types to be read from a [`JsonReader`](crate::reader::JsonReader). It is intended for use cases
//! where code is using a `JsonWriter` or `JsonReader` in the first place, to provide convenience methods
//! to directly write or read a `Serialize` or `Deserialize` in the middle of the JSON document.
//! For compatibility this module tries to match Serde JSON's behavior, but there might be small
//! differences.
//!
//! This module is _not_ intended as replacement for [Serde JSON](https://docs.rs/serde_json/latest/serde_json/index.html).
//! That crate provides greater functionality when working with JSON in the context of Serde, and likely
//! also offers better performance.
//!
//! To enable this optional integration, specify the `serde` feature in your `Cargo.toml` file
//! for the dependency on this crate:
//! ```toml
//! [dependencies]
//! struson = { version = "...", features = ["serde"] }
//! ```
//!
//! The most convenient way to use the Serde integration is by using [`JsonWriter::serialize_value`](crate::writer::JsonWriter::serialize_value)
//! and [`JsonReader::deserialize_next`](crate::reader::JsonReader::deserialize_next).\
//! Alternatively [`JsonWriterSerializer`] and [`JsonReaderDeserializer`]
//! can be used directly, but that is rarely necessary.
//!
//! # Usage examples
//!
//! ## Serialization
//! ```
//! # use struson::writer::*;
//! # use serde::*;
//! // In this example JSON bytes are stored in a Vec;
//! // normally they would be written to a file or network connection
//! let mut writer = Vec::<u8>::new();
//! let mut json_writer = JsonStreamWriter::new(&mut writer);
//!
//! // Start writing the enclosing data using the regular JsonWriter methods
//! json_writer.begin_object()?;
//! json_writer.name("outer")?;
//!
//! #[derive(Serialize)]
//! struct MyStruct {
//!     text: String,
//!     number: u64,
//! }
//!
//! let value = MyStruct {
//!     text: "some text".to_owned(),
//!     number: 5,
//! };
//! // Serialize the value as next JSON value
//! json_writer.serialize_value(&value)?;
//!
//! // Write the remainder of the enclosing data
//! json_writer.end_object()?;
//!
//! // Ensures that the JSON document is complete and flushes the buffer
//! json_writer.finish_document()?;
//!
//! let json = String::from_utf8(writer)?;
//! assert_eq!(
//!     json,
//!     r#"{"outer":{"text":"some text","number":5}}"#
//! );
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! # Deserialization
//! ```
//! # use struson::reader::*;
//! # use struson::reader::json_path::*;
//! # use serde::*;
//! // In this example JSON data comes from a string;
//! // normally it would come from a file or a network connection
//! let json = r#"{"outer": {"text": "some text", "number": 5}}"#;
//! let mut json_reader = JsonStreamReader::new(json.as_bytes());
//!
//! // Skip outer data using the regular JsonReader methods
//! json_reader.seek_to(&json_path!["outer"])?;
//!
//! #[derive(Deserialize, PartialEq, Debug)]
//! struct MyStruct {
//!     text: String,
//!     number: u64,
//! }
//!
//! let value: MyStruct = json_reader.deserialize_next()?;
//!
//! // Skip the remainder of the JSON document
//! json_reader.skip_to_top_level()?;
//!
//! // Ensures that there is no trailing data
//! json_reader.consume_trailing_whitespace()?;
//!
//! assert_eq!(
//!     value,
//!     MyStruct { text: "some text".to_owned(), number: 5 }
//! );
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

// Re-export everything directly under `serde`; mainly because the sub-modules do not
// contain many structs and enums and to flatten documentation hierarchy
mod de;
pub use de::*;
mod ser;
pub use ser::*;
