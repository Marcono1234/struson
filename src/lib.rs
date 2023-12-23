#![warn(missing_docs)]
// Enable 'unused' warnings for doc tests (are disabled by default)
#![doc(test(no_crate_inject))]
#![doc(test(attr(warn(unused))))]
// Fail on warnings in doc tests
#![doc(test(attr(deny(warnings))))]
// When `docsrs` configuration flag is set enable banner for features in documentation
// See https://stackoverflow.com/q/61417452
#![cfg_attr(docsrs, feature(doc_auto_cfg))]

//! Struson is an [RFC 8259](https://www.rfc-editor.org/rfc/rfc8259.html) compliant streaming JSON reader and writer.
//!
//! Its main purpose is allowing to read and write JSON data in a memory efficient way without having to store the
//! complete JSON document structure in memory. It is however *not* an object mapper which converts structs
//! to JSON and vice versa, a dedicated library such as [Serde](https://github.com/serde-rs/json) should be
//! used for that.
//!
//! The API of Struson was inspired by the streaming API of the Java library [Gson](https://github.com/google/gson).
//! It is rather low-level and corresponds to the elements of a JSON document, with little
//! abstraction on top of it, allowing to read and write any valid JSON document regardless
//! of its structure or content.
//!
//! # Terminology
//!
//! This crate uses the same terminology as the JSON specification:
//!
//! - *object*: `{ ... }`
//!   - *member*: Entry in an object. For example the JSON object `{"a": 1}` has the member
//!     `"a": 1` where `"a"` is the member *name* and `1` is the member *value*.
//! - *array*: `[ ... ]`
//! - *literal*:
//!   - *boolean*: `true` or `false`
//!   - `null`
//! - *number*: number value, for example `123.4e+10`
//! - *string*: string value, for example `"text in \"quotes\""`
//!
//! # Usage examples
//!
//! Two variants of the API are provided:
//! - simple: ensures correct API usage at compile-time
//! - advanced: ensures correct API usage only at runtime (by panicking); more flexible and
//!   provides more functionality
//!
//! ## Simple API
//!
//! **🔬 Experimental**\
//! The simple API and its naming is currently experimental, please provide feedback [here](https://github.com/Marcono1234/struson/issues/34).
//! Any feedback is appreciated!
//!
//! ### Reading
//! See [`SimpleJsonReader`](crate::reader::simple::SimpleJsonReader).
//!
//! ```
//! # #[cfg(feature = "experimental")]
//! # {
//! # use struson::reader::simple::*;
//! // In this example JSON data comes from a string;
//! // normally it would come from a file or a network connection
//! let json_reader = SimpleJsonReader::new(r#"["a", "short", "example"]"#.as_bytes());
//! let mut words = Vec::<String>::new();
//! json_reader.next_array_items(|item_reader| {
//!     let word = item_reader.next_string()?;
//!     words.push(word);
//!     Ok(())
//! })?;
//! assert_eq!(words, vec!["a", "short", "example"]);
//! # }
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! ### Writing
//! See [`SimpleJsonWriter`](crate::writer::simple::SimpleJsonWriter).
//!
//! ```
//! # #[cfg(feature = "experimental")]
//! # {
//! # use struson::writer::simple::*;
//! // In this example JSON bytes are stored in a Vec;
//! // normally they would be written to a file or network connection
//! let mut writer = Vec::<u8>::new();
//! let json_writer = SimpleJsonWriter::new(&mut writer);
//! json_writer.object_value(|object_writer| {
//!     object_writer.number_member("a", 1)?;
//!     object_writer.bool_member("b", true)?;
//!     Ok(())
//! })?;
//!
//! let json = String::from_utf8(writer)?;
//! assert_eq!(json, r#"{"a":1,"b":true}"#);
//! # }
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! ## Advanced API
//!
//! ### Reading
//! See [`JsonStreamReader`](crate::reader::JsonStreamReader).
//!
//! ```
//! # use struson::reader::*;
//! // In this example JSON data comes from a string;
//! // normally it would come from a file or a network connection
//! let json = r#"{"a": [1, true]}"#;
//! let mut json_reader = JsonStreamReader::new(json.as_bytes());
//!
//! json_reader.begin_object()?;
//! assert_eq!(json_reader.next_name()?, "a");
//!
//! json_reader.begin_array()?;
//! assert_eq!(json_reader.next_number::<u32>()??, 1);
//! assert_eq!(json_reader.next_bool()?, true);
//! json_reader.end_array()?;
//!
//! json_reader.end_object()?;
//! // Ensures that there is no trailing data
//! json_reader.consume_trailing_whitespace()?;
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! ### Writing
//! See [`JsonStreamWriter`](crate::writer::JsonStreamWriter).
//!
//! ```
//! # use struson::writer::*;
//! // In this example JSON bytes are stored in a Vec;
//! // normally they would be written to a file or network connection
//! let mut writer = Vec::<u8>::new();
//! let mut json_writer = JsonStreamWriter::new(&mut writer);
//!
//! json_writer.begin_object()?;
//! json_writer.name("a")?;
//!
//! json_writer.begin_array()?;
//! json_writer.number_value(1)?;
//! json_writer.bool_value(true)?;
//! json_writer.end_array()?;
//!
//! json_writer.end_object()?;
//! // Ensures that the JSON document is complete and flushes the buffer
//! json_writer.finish_document()?;
//!
//! let json = String::from_utf8(writer)?;
//! assert_eq!(json, r#"{"a":[1,true]}"#);
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! # Serde integration
//! Optional integration with [Serde](https://docs.rs/serde/latest/serde/) exists to
//! allow writing a `Serialize` to a `JsonWriter` and reading a `Deserialize` from
//! a `JsonReader`. See the [`serde`] module of this crate for more information.

pub mod reader;
pub mod writer;

#[cfg(feature = "serde")]
pub mod serde;

mod json_number;
mod utf8;
