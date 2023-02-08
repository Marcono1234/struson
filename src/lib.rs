#![warn(missing_docs)]
#![forbid(unsafe_code)]
// Allow needless `return` because that makes it sometimes more obvious that
// an expression is the result of the function
#![allow(clippy::needless_return)]
// Allow `assert_eq!(true, ...)` because in some cases it is used to check a bool
// value and not a 'flag' / 'state', and `assert_eq!` makes that more explicit
#![allow(clippy::bool_assert_comparison)]
// Enable 'unused' warnings for doc tests (are disabled by default)
#![doc(test(no_crate_inject))]
#![doc(test(attr(warn(unused))))]
// Fail on warnings in doc tests
#![doc(test(attr(deny(warnings))))]

//! Ron is a [RFC 8259](https://www.rfc-editor.org/rfc/rfc8259.html) compliant streaming JSON reader and writer.
//!
//! Its main purpose is allowing to read and write JSON data in a memory efficient way without having to store the
//! complete JSON document structure in memory. It is however *not* an object mapper which converts structs
//! to JSON and vice versa, a dedicated library such as [Serde](https://github.com/serde-rs/json) should be
//! used for that.
//!
//! The API of Ron was inspired by the streaming API of the Java library [Gson](https://github.com/google/gson).
//!
//! # Terminology
//!
//! This crate uses the same terminology as the JSON specification:
//!
//! - *object*: `{ ... }`
//!   - *member*: Entry in an object. For example the JSON object `{"a": 1}` has the member
//!     `"a": 1` where `"a"` is the member *name* and `1` is the member *value*.
//! - *array*: `[ ... ]`
//! - *literal*: `true`, `false` or `null`
//! - *number*: number value, for example `123.4e+10`
//! - *string*: string value, for example `"text in \"quotes\""`
//!
//! # Usage examples
//!
//! ## Reading
//!
//! ```
//! # use ron::reader::*;
//! // In this example JSON data comes from a string;
//! // normally it would come from a file or a network connection
//! let json = r#"{"a": [1, true]}"#;
//! let mut json_reader = JsonStreamReader::new(json.as_bytes());
//!
//! json_reader.begin_object()?;
//! assert_eq!(json_reader.next_name()?, "a");
//!
//! json_reader.begin_array()?;
//! assert_eq!(1_u32, json_reader.next_number()??);
//! assert_eq!(true, json_reader.next_bool()?);
//! json_reader.end_array()?;
//!
//! json_reader.end_object()?;
//! // Ensures that there is no trailing data
//! json_reader.consume_trailing_whitespace()?;
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! ## Writing
//! ```
//! # use ron::writer::*;
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
//! assert_eq!(r#"{"a":[1,true]}"#, std::str::from_utf8(&writer)?);
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

pub mod reader;
pub mod writer;

mod json_number;
