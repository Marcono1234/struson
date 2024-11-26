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
//! It has to be enabled by specifying the `simple-api` feature in `Cargo.toml`:
//! ```toml
//! [dependencies]
//! struson = { version = "...", features = ["simple-api"] }
//! ```
//! Any feedback is appreciated!
//!
//! ### Reading
//! See [`SimpleJsonReader`](crate::reader::simple::SimpleJsonReader).
//!
//! ```
//! # #[cfg(feature = "simple-api")]
//! # {
//! use struson::reader::simple::*;
//!
//! // In this example JSON data comes from a string;
//! // normally it would come from a file or a network connection
//! let json_reader = SimpleJsonReader::new(r#"["a", "short", "example"]"#.as_bytes());
//! let mut words = Vec::<String>::new();
//! json_reader.read_array_items(|item_reader| {
//!     let word = item_reader.read_string()?;
//!     words.push(word);
//!     Ok(())
//! })?;
//! assert_eq!(words, vec!["a", "short", "example"]);
//! # }
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! For reading nested values, the methods [`read_seeked`](crate::reader::simple::ValueReader::read_seeked)
//! and [`read_seeked_multi`](crate::reader::simple::ValueReader::read_seeked_multi) can be used:
//! ```
//! # #[cfg(feature = "simple-api")]
//! # {
//! use struson::reader::simple::*;
//! use struson::reader::simple::multi_json_path::multi_json_path;
//!
//! // In this example JSON data comes from a string;
//! // normally it would come from a file or a network connection
//! let json = r#"{
//!     "users": [
//!         {"name": "John", "age": 32},
//!         {"name": "Jane", "age": 41}
//!     ]
//! }"#;
//! let json_reader = SimpleJsonReader::new(json.as_bytes());
//!
//! let mut ages = Vec::<u32>::new();
//! // Select the ages of all users
//! let json_path = multi_json_path!["users", [*], "age"];
//! json_reader.read_seeked_multi(&json_path, false, |value_reader| {
//!     let age = value_reader.read_number()??;
//!     ages.push(age);
//!     Ok(())
//! })?;
//! assert_eq!(ages, vec![32, 41]);
//! # }
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! ### Writing
//! See [`SimpleJsonWriter`](crate::writer::simple::SimpleJsonWriter).
//!
//! ```
//! # #[cfg(feature = "simple-api")]
//! # {
//! use struson::writer::simple::*;
//!
//! // In this example JSON bytes are stored in a Vec;
//! // normally they would be written to a file or network connection
//! let mut writer = Vec::<u8>::new();
//! let json_writer = SimpleJsonWriter::new(&mut writer);
//! json_writer.write_object(|object_writer| {
//!     object_writer.write_number_member("a", 1)?;
//!     object_writer.write_bool_member("b", true)?;
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
//! use struson::reader::*;
//!
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
//! use struson::writer::*;
//!
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
//! a `JsonReader`. See the [`serde` module](crate::serde) of this crate for more information.

pub mod reader;
pub mod writer;

#[cfg(feature = "serde")]
pub mod serde;

mod json_number;
mod utf8;
