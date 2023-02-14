//! Module for reading JSON data
//!
//! [`JsonReader`] is the general trait for JSON readers, [`JsonStreamReader`] is an implementation
//! of it which reads a JSON document from a [`Read`] in a streaming way.
use crate::{
    json_number::consume_json_number,
    writer::{JsonNumberError, JsonWriter},
};

/// Module for JSONPath
///
/// A JSONPath consists of zero or more [`JsonPathPiece`] elements which either represent the index of a
/// JSON array item or the name of a JSON object member. These elements combined form the _path_ to a value
/// in a JSON document.
///
/// The macro [`json_path!`](json_path::json_path) and the function [`parse_json_path`](json_path::parse_json_path)
/// can be used to create a JSONPath in a concise way.
///
/// JSONPath was originally specified in [this article](https://goessner.net/articles/JsonPath/). However,
/// this module only supports a small subset needed for JSON reader functionality, most notably for reporting
/// the location of errors and for [`JsonReader::seek_to`].
///
/// Consider for example the following code:
/// ```
/// # use ron::reader::json_path::*;
/// vec![
///     JsonPathPiece::ObjectMember("a".to_owned()),
///     JsonPathPiece::ArrayItem(2),
/// ]
/// # ;
/// ```
/// It means: Within a JSON object the member with name "a", and assuming the value of that member is
/// a JSON array, of that array the item at index 2 (starting at 0). The string representation of the
/// path in dot-notation would be `a[2]`.  
/// For example in the JSON string `{"a": [0.5, 1.5, 2.5]}` it would point to the value `2.5`.
pub mod json_path {
    use std::str::FromStr;

    use thiserror::Error;

    /// A piece of a JSONPath
    ///
    /// A piece can either represent the index of a JSON array item or the name of a JSON object member.
    #[derive(PartialEq, Eq, Clone, Debug)]
    pub enum JsonPathPiece {
        /// Index (starting at 0) of a JSON array item
        ArrayItem(u32),
        /// Name of a JSON object member
        ObjectMember(String),
    }

    /// Creates a [`JsonPathPiece::ArrayItem`] with the number as index
    impl From<u32> for JsonPathPiece {
        fn from(v: u32) -> Self {
            JsonPathPiece::ArrayItem(v)
        }
    }

    /// Creates a [`JsonPathPiece::ObjectMember`] with the string as member name
    impl From<String> for JsonPathPiece {
        fn from(v: String) -> Self {
            JsonPathPiece::ObjectMember(v)
        }
    }

    /// Creates a [`JsonPathPiece::ObjectMember`] with the string as member name
    impl From<&str> for JsonPathPiece {
        fn from(v: &str) -> Self {
            JsonPathPiece::ObjectMember(v.to_string())
        }
    }

    /// A JSONPath
    ///
    /// A JSONPath as represented by this module are zero or more [`JsonPathPiece`] elements.
    /// The macro [`json_path!`] and the function [`parse_json_path`] can be used to create
    /// a JSONPath in a concise way.
    /* TODO: Check if it is somehow possible to implement Display for this (and reuse code from format_abs_json_path then) */
    pub type JsonPath = [JsonPathPiece];

    pub(crate) fn format_abs_json_path(json_path: &JsonPath) -> String {
        "$".to_string()
            + json_path
                .iter()
                .map(|p| match p {
                    JsonPathPiece::ArrayItem(index) => {
                        "[".to_owned() + index.to_string().as_str() + "]"
                    }
                    JsonPathPiece::ObjectMember(name) => ".".to_owned() + name.as_str(),
                })
                .collect::<String>()
                .as_str()
    }

    /// Error which occurred while [parsing a JSONPath](parse_json_path)
    #[derive(Error, Clone, Debug)]
    #[error("parse error at index {index}: {message}")]
    pub struct JsonPathParseError {
        /// Index (starting at 0) where the error occurred within the string
        pub index: usize,
        /// Message describing why the error occurred
        pub message: String,
    }

    /// Parses a JSONPath in dot-notation, for example `outer[4].inner`
    ///
    /// This is a convenience function which allows obtaining a vector of [`JsonPathPiece`] from a string form.
    /// The path string must not start with `$` (respectively `$.`) and member names are limited to contain only
    /// `a`-`z`, `A`-`Z`, `0`-`9`, `-` and `_`. The path string must not be empty. For malformed path strings
    /// an error is returned.
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::json_path::*;
    /// let json_path = parse_json_path("outer[1].inner[2][3]")?;
    /// assert_eq!(
    ///     json_path,
    ///     vec![
    ///         JsonPathPiece::ObjectMember("outer".to_owned()),
    ///         JsonPathPiece::ArrayItem(1),
    ///         JsonPathPiece::ObjectMember("inner".to_owned()),
    ///         JsonPathPiece::ArrayItem(2),
    ///         JsonPathPiece::ArrayItem(3),
    ///     ]
    /// );
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    /* TODO: Is there a proper specification (maybe even RFC?) for JSONPath, if so, should this function follow that specification? */
    pub fn parse_json_path(path: &str) -> Result<Vec<JsonPathPiece>, JsonPathParseError> {
        if path.is_empty() {
            return Err(JsonPathParseError {
                index: 0,
                message: "Empty path".to_owned(),
            });
        }

        fn find<T: PartialEq>(slice: &[T], t: T, start: usize) -> Option<usize> {
            (start..slice.len()).find(|&i| slice[i] == t)
        }
        /// Finds the first occurrence of [t1] or [t2]
        fn find_any<T: PartialEq>(slice: &[T], t1: T, t2: T, start: usize) -> Option<usize> {
            (start..slice.len()).find(|&i| slice[i] == t1 || slice[i] == t2)
        }

        let path_bytes = path.as_bytes();

        if path_bytes[0] == b'.' {
            return Err(JsonPathParseError {
                index: 0,
                message: "Leading '.' is not allowed".to_owned(),
            });
        }

        let mut parsed_path = Vec::new();
        let mut index = 0;
        // Perform this check here because first member name cannot have leading '.'
        let mut is_array_item = path_bytes[0] == b'[';

        loop {
            if is_array_item {
                index += 1;
                let end_index = match find(path_bytes, b']', index) {
                    None => {
                        return Err(JsonPathParseError {
                            index,
                            message: "Missing ']' for array index".to_owned(),
                        })
                    }
                    Some(i) => i,
                };
                if end_index == index {
                    return Err(JsonPathParseError {
                        index,
                        message: "Missing index value".to_owned(),
                    });
                }
                if path_bytes[index] == b'0' && end_index != index + 1 {
                    return Err(JsonPathParseError {
                        index,
                        message: "Leading 0 is not allowed".to_owned(),
                    });
                }

                #[allow(clippy::needless_range_loop)] // Suggested replacement is too verbose
                for i in index..end_index {
                    if !(b'0'..=b'9').contains(&path_bytes[i]) {
                        return Err(JsonPathParseError {
                            index: i,
                            message: "Invalid index digit".to_owned(),
                        });
                    }
                }
                let path_index =
                    u32::from_str(&path[index..end_index]).map_err(|e| JsonPathParseError {
                        index,
                        message: "Invalid index value: ".to_owned() + e.to_string().as_str(),
                    })?;
                parsed_path.push(JsonPathPiece::ArrayItem(path_index));
                index = end_index + 1;
            } else {
                let end_index = find_any(path_bytes, b'.', b'[', index).unwrap_or(path_bytes.len());
                if end_index == index {
                    return Err(JsonPathParseError {
                        index,
                        message: "Missing member name".to_owned(),
                    });
                }

                #[allow(clippy::needless_range_loop)] // Suggested replacement is too verbose
                for i in index..end_index {
                    let b = path_bytes[i];
                    if !((b'a'..=b'z').contains(&b)
                        || (b'A'..=b'Z').contains(&b)
                        || (b'0'..=b'9').contains(&b)
                        || b == b'-'
                        || b == b'_')
                    {
                        return Err(JsonPathParseError {
                            index: i,
                            message: "Unsupported char in member name".to_owned(),
                        });
                    }
                }

                parsed_path.push(JsonPathPiece::ObjectMember(
                    path[index..end_index].to_string(),
                ));
                index = end_index;
            }

            if index >= path_bytes.len() {
                break;
            }
            match path_bytes[index] {
                b'.' => {
                    is_array_item = false;
                    index += 1;
                }
                b'[' => {
                    is_array_item = true;
                    // Don't have to skip '[' here, that is done at the beginning of the loop
                }
                _ => {
                    return Err(JsonPathParseError {
                        index,
                        message: "Expecting either '.' or '['".to_owned(),
                    })
                }
            }
        }

        Ok(parsed_path)
    }

    /// Creates a JSONPath from path pieces
    ///
    /// The arguments to this macro represent the path pieces:
    /// - numbers of type `u32` are converted to [`JsonPathPiece::ArrayItem`]
    /// - strings are converted to [`JsonPathPiece::ObjectMember`]
    ///
    /// At least one path piece argument must be provided.
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::json_path::*;
    /// let json_path = json_path!["outer", 3, "inner"];
    /// assert_eq!(
    ///     json_path,
    ///     [
    ///         JsonPathPiece::ObjectMember("outer".to_owned()),
    ///         JsonPathPiece::ArrayItem(3),
    ///         JsonPathPiece::ObjectMember("inner".to_owned()),
    ///     ]
    /// );
    /// ```
    /*
     * TODO: Ideally in the future not expose this at the crate root but only from the `json_path` module
     *       however, that is apparently not easily possible yet, see https://users.rust-lang.org/t/how-to-namespace-a-macro-rules-macro-within-a-module-or-macro-export-it-without-polluting-the-top-level-namespace/63779/5
     * TODO: Instead of returning [...], should this directly return &[...] to make usage easier?
     */
    #[macro_export]
    macro_rules! json_path {
        ( $( $piece:expr ),+ ) => {
            {
                [
                    $(
                        $crate::reader::json_path::JsonPathPiece::from($piece),
                    )*
                ]
            }
        };
    }

    // Re-export the macro to be available under the `ron::reader::json_path` module path
    #[doc(inline)]
    pub use json_path;

    #[cfg(test)]
    mod tests {
        use super::*;

        type TestResult = Result<(), Box<dyn std::error::Error>>;

        #[test]
        fn test_format_abs_json_path() {
            assert_eq!("$", format_abs_json_path(&Vec::new()));

            assert_eq!("$[2]", format_abs_json_path(&[JsonPathPiece::ArrayItem(2)]));
            assert_eq!(
                "$[2][3]",
                format_abs_json_path(&[JsonPathPiece::ArrayItem(2), JsonPathPiece::ArrayItem(3)])
            );
            assert_eq!(
                "$[2].a",
                format_abs_json_path(&[
                    JsonPathPiece::ArrayItem(2),
                    JsonPathPiece::ObjectMember("a".to_owned())
                ])
            );

            assert_eq!(
                "$.a",
                format_abs_json_path(&[JsonPathPiece::ObjectMember("a".to_owned())])
            );
            assert_eq!(
                "$.a.b",
                format_abs_json_path(&[
                    JsonPathPiece::ObjectMember("a".to_owned()),
                    JsonPathPiece::ObjectMember("b".to_owned())
                ])
            );
            assert_eq!(
                "$.a[2]",
                format_abs_json_path(&[
                    JsonPathPiece::ObjectMember("a".to_owned()),
                    JsonPathPiece::ArrayItem(2)
                ])
            );
        }

        #[test]
        fn test_parse_json_path() -> TestResult {
            assert_eq!(
                vec![JsonPathPiece::ObjectMember("abc".to_owned())],
                parse_json_path("abc")?
            );
            assert_eq!(vec![JsonPathPiece::ArrayItem(0)], parse_json_path("[0]")?);
            assert_eq!(vec![JsonPathPiece::ArrayItem(34)], parse_json_path("[34]")?);

            assert_eq!(
                vec![
                    JsonPathPiece::ObjectMember("ab".to_owned()),
                    JsonPathPiece::ObjectMember("cd".to_owned()),
                    JsonPathPiece::ArrayItem(12),
                    JsonPathPiece::ObjectMember("34".to_owned()),
                    JsonPathPiece::ArrayItem(56),
                    JsonPathPiece::ArrayItem(78)
                ],
                parse_json_path("ab.cd[12].34[56][78]")?
            );

            fn assert_parse_error(path: &str, expected_index: usize, expected_message: &str) {
                match parse_json_path(path) {
                    Err(e) => {
                        assert_eq!(expected_index, e.index);
                        assert_eq!(expected_message, e.message);
                    }
                    Ok(_) => panic!("Should have failed for: {path}"),
                }
            }

            assert_parse_error("", 0, "Empty path");
            assert_parse_error(".a", 0, "Leading '.' is not allowed");
            assert_parse_error("[", 1, "Missing ']' for array index");
            assert_parse_error("[1", 1, "Missing ']' for array index");
            assert_parse_error("[1.a]", 2, "Invalid index digit");
            assert_parse_error("[1a2]", 2, "Invalid index digit");
            assert_parse_error("[01]", 1, "Leading 0 is not allowed");
            assert_parse_error("[00]", 1, "Leading 0 is not allowed");
            assert_parse_error("[-1]", 1, "Invalid index digit");
            // TODO: Should this test really check for specific Rust library message?
            assert_parse_error(
                "[99999999999999999999999999999999999999999999]",
                1,
                "Invalid index value: number too large to fit in target type",
            );
            assert_parse_error("[1[0]]", 2, "Invalid index digit");
            assert_parse_error("[a]", 1, "Invalid index digit");
            assert_parse_error("[1]1]", 3, "Expecting either '.' or '['");
            assert_parse_error("[1]a", 3, "Expecting either '.' or '['");
            assert_parse_error("a.", 2, "Missing member name");
            assert_parse_error("a..b", 2, "Missing member name");
            assert_parse_error("a.[1]", 2, "Missing member name");
            assert_parse_error("%a", 0, "Unsupported char in member name");
            assert_parse_error("a%", 1, "Unsupported char in member name");

            Ok(())
        }

        #[test]
        fn macro_json_path() {
            assert_eq!(json_path![3], [JsonPathPiece::ArrayItem(3)]);
            assert_eq!(
                json_path!["a"],
                [JsonPathPiece::ObjectMember("a".to_owned())]
            );
            assert_eq!(
                json_path!["a".to_owned()],
                [JsonPathPiece::ObjectMember("a".to_owned())]
            );
            assert_eq!(
                json_path!["outer", 1, "inner".to_owned(), 2],
                [
                    JsonPathPiece::ObjectMember("outer".to_owned()),
                    JsonPathPiece::ArrayItem(1),
                    JsonPathPiece::ObjectMember("inner".to_owned()),
                    JsonPathPiece::ArrayItem(2),
                ]
            );
        }
    }
}

use thiserror::Error;

use std::{
    fmt::{Debug, Display},
    io::{ErrorKind, Read},
    str::FromStr,
};

use self::json_path::{format_abs_json_path, JsonPath, JsonPathPiece};
// Ignore false positive for unused import of `json_path!` macro
#[allow(unused_imports)]
use self::json_path::json_path;

type IoError = std::io::Error;

/// Type of a JSON value
#[derive(PartialEq, Eq, Clone, Copy, strum_macros::Display, Debug)]
pub enum ValueType {
    /// JSON array: `[ ... ]`
    Array,
    /// JSON object: `{ ... }`
    Object,
    /// JSON string value, for example `"text in \"quotes\""`
    String,
    /// JSON number value, for example `123.4e+10`
    Number,
    /// JSON boolean value, `true` or `false`
    Boolean,
    /// JSON `null`
    Null,
    // No EndOfDocument because peeking after top-level element is a logic error

    // No ArrayEnd and ObjectEnd, should use has_next()
}

/// Location of an error which occurred while reading a JSON document
///
/// A location consists of a JSONPath, the line and column number. Consider the following malformed
/// JSON document (`@` being the malformed character):
/// ```json
/// {
///   "a": @
/// }
/// ```
/// The location would be:
/// - path: `$.a`  
///   The error occurred for the member with name "a"
/// - line: 1  
///   Line numbering starts at 0 and the error occurred in the second line
/// - column: 7  
///   Column numbering starts at 0 and the `@` is the 8th character in that line, respectively
///   there are 7 characters in front of it
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct JsonErrorLocation {
    /// [JSONPath](https://goessner.net/articles/JsonPath/) of the error in dot-notation, for example `$.outer[4].second`
    ///
    /// This path is mainly intended to help troubleshooting, it should not be parsed in any way since it might be ambiguous
    /// or incorrect for certain member names. For example when a member name is `"address.street"` it would erroneously be
    /// considered to consist of two separate names `"address"` and a nested member named `"street"`.
    ///
    /// The last piece of the path cannot accurately point to the error location in all cases because errors can occur at
    /// any position in the JSON document and some cannot be described properly using a JSONPath. The last path piece has
    /// the following meaning:
    ///
    /// - Array item index: Index of the currently processed item, or index of the potential next item
    ///
    ///   For example the path `$[2]` means, depending on the error type, that either the error occurred in front of the
    ///   item at index 2 or the end of the array, for example when a comma is missing. Or it means that parsing the
    ///   item at index 2 failed, for example because it is a malformed number value. Note that array indices start at 0.
    ///
    ///   In general the index is incremented once a value in an array was fully consumed, which results in the
    ///   behavior described above.
    ///
    /// - Object member name: Name of the previously read member, or name of the current member
    ///
    ///   For example the path `$.a` means, depending on the error type, that either the error occurred for the value
    ///   of the member with name "a", for example when the value of the member is malformed. Or it means that parsing
    ///   the name of the member after "a" or the end of the object failed.  
    ///   The special name `<?>` is used to indicate that a JSON object was started, but the name of the first member
    ///   has not been consumed yet. It is also used when skipping values (for example with [`JsonReader::skip_value`])
    ///   and updating the path is [disabled in the `ReaderSettings`](ReaderSettings::update_path_during_skip).
    ///
    /// For the exact location of the error the [`line`](Self::line) and [`column`](Self::column) values should be used.
    pub path: String,
    /// Line number of the error, starting at 0
    ///
    /// The characters _CR_ (U+000D), _LF_ (U+000A) and _CR LF_ are considered line breaks. Other characters and
    /// escaped line breaks in member names and string values are not considered line breaks.
    pub line: u32,
    /// Character column of the error within the current line, starting at 0
    ///
    /// For all Unicode characters this value is incremented only by one, regardless of whether some encodings
    /// such as UTF-8 might use more than one byte for the character, or whether encodings such as UTF-16
    /// might use two characters (a *surrogate pair*) to encode the character. Similarly the tab character
    /// (U+0009) is also considered a single character even though code editors might display it as if it
    /// consisted of more than one space character.
    pub column: u32,
}

impl Display for JsonErrorLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "line {}, column {} at path {}",
            self.line, self.column, self.path
        )
    }
}

/// JSON syntax error
#[derive(Error, PartialEq, Eq, Clone, Debug)]
#[error("JSON syntax error {kind} at {location}")]
pub struct JsonSyntaxError {
    /// Kind of the error
    pub kind: SyntaxErrorKind,
    /// Location where the error occurred in the JSON document
    pub location: JsonErrorLocation,
}

/// Describes why a syntax error occurred
#[derive(PartialEq, Eq, Clone, Copy, strum_macros::Display, Debug)]
pub enum SyntaxErrorKind {
    /// A comment was encountered, but comments are not enabled in the [`ReaderSettings`]
    CommentsNotEnabled,
    /// A comment is incomplete
    IncompleteComment,
    /// A block comment is missing the closing `*/`
    BlockCommentNotClosed,

    /// A literal value is incomplete or invalid, for example `tru` instead of `true`
    InvalidLiteral,
    /// There is unexpected trailing data after a literal, for example `truey` instead of `true`
    TrailingDataAfterLiteral,
    /// A closing bracket (`]` or `}`) was encountered where it was not expected
    UnexpectedClosingBracket,
    /// A comma (`,`) was encountered where it was not expected
    UnexpectedComma,
    /// A comma (`,`) is missing between array elements or object members
    MissingComma,
    /// A trailing comma (for example in `[1,]`) was used, but trailing commas are not enabled in the [`ReaderSettings`]
    TrailingCommaNotEnabled,
    /// A colon (`:`) was encountered where it was not expected
    UnexpectedColon,
    /// A colon (`:`) is missing between member name and member value
    MissingColon,
    /// A JSON number is malformed, for example `01` (leading 0 is not allowed)
    MalformedNumber,
    /// There is unexpected trailing data after a number, for example `123a`
    TrailingDataAfterNumber,
    /// A member name or the end of an object (`}`) was expected but something else was encountered
    ExpectingMemberNameOrObjectEnd,
    /// The JSON data is malformed for a reason other than any of the other kinds
    ///
    /// This is usually the case when Unicode characters other than the ones used as start or end of JSON values
    /// (such as `"`, `[`, `}` ...) are encountered.
    MalformedJson,

    /// A control character was encountered in the raw JSON data of a member name or string value
    ///
    /// The JSON specification requires that Unicode characters in the range from `0x00` to `0x1F` (inclusive) must be
    /// escaped when part of member name or string value. This can be done either with a `\uXXXX` escape or with a
    /// short escape sequence such as `\n`, if one exists.
    NotEscapedControlCharacter,
    /// An unknown escape sequence (`\...`) was encountered
    UnknownEscapeSequence,
    /// A malformed escape sequence was encountered, for example `\u00` instead of `\u0000`
    MalformedEscapeSequence,
    /// An unpaired UTF-16 surrogate pair was encountered in a member name or a string value
    ///
    /// Since Rust strings must consist of valid UTF-8 data, UTF-16 surrogate characters in the form
    /// of escape sequences in JSON (`\uXXXX`) must always form a valid surrogate pair. For example
    /// the character U+10FFFF would either have to be in raw form in the UTF-8 data of the JSON document
    /// or be encoded as the escape sequence pair `\uDBFF\uDFFF`.
    UnpairedSurrogatePairEscapeSequence,

    /// The JSON document is incomplete, for example a closing `]` is missing
    IncompleteDocument,
    /// Unexpected trailing data was detected at the end of the JSON document
    ///
    /// This error kind is used by [`JsonReader::consume_trailing_whitespace`].
    TrailingData,
}

/// Describes why the JSON document is considered to have an unexpected structure
#[derive(PartialEq, Eq, Clone, strum_macros::Display, Debug)]
pub enum UnexpectedStructureKind {
    /// A JSON array has fewer items than expected
    TooShortArray {
        /// Index (starting at 0) of the expected item
        expected_index: u32,
    },
    /// A JSON object does not have a member with a certain name
    MissingObjectMember {
        /// Name of the expected member
        member_name: String,
    },
    /// A JSON array or object has fewer elements than expected
    ///
    /// This is a more general version than [`TooShortArray`](UnexpectedStructureKind::TooShortArray)
    /// and [`MissingObjectMember`](UnexpectedStructureKind::MissingObjectMember) where it is only known
    /// that more elements are expected without knowing the expected index or member name.
    FewerElementsThanExpected,
    /// A JSON array or object has more elements than expected
    MoreElementsThanExpected,
}

/// Error which occurred while reading from a JSON reader
#[derive(Error, Debug)]
pub enum ReaderError {
    /// A syntax error was encountered
    #[error("syntax error: {0}")]
    SyntaxError(#[from] JsonSyntaxError),
    /// The next JSON value had an unexpected type
    ///
    /// This error can occur for example when trying to read a JSON number when the next value is actually
    /// a JSON boolean.
    #[error("expected JSON value type {expected} but got {actual} at {location}")]
    UnexpectedValueType {
        /// The expected JSON value type
        expected: ValueType,
        /// The actual JSON value type
        actual: ValueType,
        /// Location where the error occurred in the JSON document
        location: JsonErrorLocation,
    },
    /// The JSON document had an unexpected structure
    ///
    /// This error occurs when trying to consume more elements than a JSON array or object has, or
    /// when trying to end a JSON array or object when there are still unprocessed elements in it.
    /// If these remaining elements should be ignored they can be skipped like this:
    /// ```
    /// # use ron::reader::*;
    /// # let mut json_reader = JsonStreamReader::new("[]".as_bytes());
    /// # json_reader.begin_array()?;
    /// while json_reader.has_next()? {
    ///     json_reader.skip_value()?;
    /// }
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    /// Note: For a JSON object [`skip_name`](JsonReader::skip_name) and [`skip_value`](JsonReader::skip_value)
    /// have to be called for every member to skip its name and value.
    #[error("unexpected JSON structure {kind} at {location}")]
    UnexpectedStructure {
        /// Describes why the JSON document is considered to have an invalid structure
        kind: UnexpectedStructureKind,
        /// Location where the error occurred in the JSON document
        location: JsonErrorLocation,
    },
    /// An unsupported JSON number value was encountered
    ///
    /// See [`ReaderSettings::restrict_number_values`] for more information.
    #[error("unsupported number value at {0}")]
    // TODO: If possible also include the number string, but this is currently not easily possible
    // in all cases without duplicating code, and while still reporting the correct location
    UnsupportedNumberValue(JsonErrorLocation),
    /// An IO error occurred while trying to read from the underlying reader, or
    /// malformed UTF-8 data was encountered
    #[error("IO error: {0}")]
    IoError(#[from] IoError),
}

/// Error which occurred while calling [`JsonReader::transfer_to`]
#[derive(Error, Debug)]
pub enum TransferError {
    /// Error which occurred while readering from the JSON reader
    #[error("reader error: {0}")]
    ReaderError(#[from] ReaderError),
    /// Error which occurred while writing to the JSON writer
    #[error("writer error: {0}")]
    WriterError(#[from] IoError),
}

// TODO: Doc: Deduplicate documentation for errors and panics for value reading methods and only describe it
//       once in the documentation of JsonReader?

/// A trait for JSON readers
///
/// The methods of this reader can be divided into the following categories:
///
/// - Peeking values, without consuming them
///     - [`peek`](Self::peek): Peeks at the type of the next value
///     - [`has_next`](Self::has_next): Checks if there is a next value
/// - Reading values
///     - [`begin_array`](Self::begin_array), [`end_array`](Self::end_array): Starting and ending a JSON array
///     - [`begin_object`](Self::begin_object), [`end_object`](Self::end_object): Starting and ending a JSON object
///     - [`next_name`](Self::next_name): Reading the name of a JSON object member
///     - [`next_string`](Self::next_string), [`next_string_reader`](Self::next_string_reader): Reading a JSON string value
///     - [`next_number`](Self::next_number), [`next_number_as_string`](Self::next_number_as_string): Reading a JSON number value
///     - [`next_bool`](Self::next_bool): Reading a JSON boolean value
///     - [`next_null`](Self::next_null): Reading a JSON null value
///     - [`deserialize_next`](Self::deserialize_next): Deserializes a Serde [`Deserialize`](serde::de::Deserialize) from the next value (optional feature)
///  - Skipping values
///     - [`skip_name`](Self::skip_name): Skipping the name of a JSON object member
///     - [`skip_value`](Self::skip_value): Skipping a value
///     - [`seek_to`](Self::seek_to): Skipping values until a specified location is reached
///     - [`skip_to_top_level`](Self::skip_to_top_level): Skipping the remaining elements of all enclosing JSON arrays and objects
///  - Other:
///     - [`transfer_to`](Self::transfer_to): Reading a JSON value and writing it to a given JSON writer
///     - [`consume_trailing_whitespace`](Self::consume_trailing_whitespace): Consuming trailing whitespace at the end of the JSON document
///
/// JSON documents have at least one top-level value which can be either a JSON array, object,
/// string, number, boolean or null value. For JSON arrays and objects the opening brackets
/// must be consumed with the corresponding `begin_` method (for example [`begin_array`](Self::begin_array)) and the
/// closing bracket with the corresponding `end_` method (for example [`end_array`](Self::end_array)). JSON objects
/// consist of *members* which are name-value pairs. The name of a member can be read with
/// [`next_name`](Self::next_name) and the value with any of the value reading methods such as [`next_bool`](Self::next_bool).
///
/// It is not necessary to consume the complete JSON document, for example a user of this reader
/// can simply drop the reader once the relevant information was extracted, ignoring the remainder
/// of the JSON data. However, in that case no validation will be performed that the remainder
/// has actually valid JSON syntax. To ensure that, [`skip_to_top_level`](Self::skip_to_top_level)
/// can be used to skip (and validate) the remainder of the current top-level JSON array or object.
///
/// **Important:** Even after the top-level has been fully consumed this reader does *not*
/// automatically consume the remainder of the JSON document (which is expected to consist
/// of optional whitespace only). To verify that there is no trailing data it is necessary
/// to explicitly call [`consume_trailing_whitespace`](Self::consume_trailing_whitespace).
///
/// # Examples
/// ```
/// # use ron::reader::*;
/// // In this example JSON data comes from a string;
/// // normally it would come from a file or a network connection
/// let json = r#"{"a": [1, 2, true]}"#;
/// let mut json_reader = JsonStreamReader::new(json.as_bytes());
///
/// json_reader.begin_object()?;
/// assert_eq!(json_reader.next_name()?, "a");
///
/// json_reader.begin_array()?;
/// assert_eq!(1_u32, json_reader.next_number()??);
/// json_reader.skip_value()?;
/// assert_eq!(true, json_reader.next_bool()?);
/// json_reader.end_array()?;
///
/// json_reader.end_object()?;
/// // Ensures that there is no trailing data
/// json_reader.consume_trailing_whitespace()?;
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Error handling
/// The methods of this reader return a [`Result::Err`] when an error occurs while reading
/// the JSON document. The error can for example be caused by an IO error from the underlying
/// reader, a JSON syntax error or an unexpected structure of the JSON document.
/// See [`ReaderError`] for more details.
///
/// When encountering [`ReaderError::SyntaxError`] and [`ReaderError::IoError`] processing the
/// JSON document **must** be aborted. Trying to call any reader methods afterwards can lead
/// to unspecified behavior, such as errors, panics or incorrect data. However, no _undefined_
/// behavior occurs.
///
/// When encountering [`ReaderError::UnexpectedValueType`] or [`ReaderError::UnexpectedStructure`]
/// depending on the use case it might be possible to continue processing the JSON document
/// (except for [`seek_to`](Self::seek_to) where it might not be obvious how many elements have already been
/// skipped). However, these errors can usually be avoided by using either [`peek`](Self::peek) or [`has_next`](Self::has_next)
/// before trying to consume a value whose type is not known in advance, or for which it
/// is not known whether it is present in the JSON document.
///
/// In general it is recommended to handle errors with the `?` operator of Rust, for example
/// `json_reader.next_bool()?` and to abort processing the JSON document when an error occurs.
///
/// # Panics
/// Methods of this reader panic when used in an incorrect way. The documentation of the methods
/// describes in detail the situations when that will happen. In general all these cases are
/// related to incorrect usage by the user (such as trying to call [`end_object`](Self::end_object) when currently
/// reading a JSON array) and are unrelated to the JSON data which is processed.
pub trait JsonReader {
    /// Peeks at the type of the next value, without consuming it
    ///
    /// Peeking at the type of a value can be useful when the exact structure of a JSON document is
    /// not known in advance, or when a value could be of more than one type. The value can then be
    /// consumed with one of the other methods.
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// # let mut json_reader = JsonStreamReader::new("true".as_bytes());
    /// match json_reader.peek()? {
    ///     ValueType::Boolean => println!("A boolean: {}", json_reader.next_bool()?),
    ///     ValueType::String => println!("A string: {}", json_reader.next_string()?),
    ///     _ => panic!("Unexpected type"),
    /// }
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This method does not guarantee that the peeked value is complete or valid; consuming it
    /// (with a separate method call) can return an error when malformed JSON is detected.
    ///
    /// # Errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If there is no next value a [`ReaderError::UnexpectedStructure`] is returned. The method
    /// [`has_next`](Self::has_next) can be used to check if there is a next value.
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently expects a member name, or
    /// when called after the top-level value has already been consumed and multiple top-level
    /// values are not enabled in the [`ReaderSettings`]. Both cases indicate incorrect
    /// usage by the user and are unrelated to the JSON data.
    fn peek(&mut self) -> Result<ValueType, ReaderError>;

    /// Begins consuming a JSON object
    ///
    /// The method [`has_next`](Self::has_next) can be used to check if there is a next object member. To consume a member
    /// first call [`next_name`](Self::next_name) and afterwards one of the value reading methods such as [`next_number`](Self::next_number).
    /// At the end call [`end_object`](Self::end_object) to consume the closing bracket of the JSON object.
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// let mut json_reader = JsonStreamReader::new(r#"{"a": 1, "b": 2}"#.as_bytes());
    /// json_reader.begin_object()?;
    ///
    /// // Prints "a: 1", "b: 2"
    /// while json_reader.has_next()? {
    ///     let name = json_reader.next_name()?;
    ///     let value: u32 = json_reader.next_number()??;
    ///     println!("{name}: {value}");
    /// }
    ///
    /// json_reader.end_object()?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If there is no next value a [`ReaderError::UnexpectedStructure`] is returned. The [`has_next`](Self::has_next)
    /// method can be used to check if there is a next value.
    ///
    /// If the next value is not a JSON object but is a value of a different type
    /// a [`ReaderError::UnexpectedValueType`] is returned. The [`peek`](Self::peek) method can be used to
    /// check the type if it is not known in advance.
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently expects a member name, or
    /// when called after the top-level value has already been consumed and multiple top-level
    /// values are not enabled in the [`ReaderSettings`]. Both cases indicate incorrect
    /// usage by the user and are unrelated to the JSON data.
    fn begin_object(&mut self) -> Result<(), ReaderError>;

    /// Consumes the closing bracket `}` of the current JSON object
    ///
    /// This method is used to end a JSON object started by [`begin_object`](Self::begin_object).
    ///
    /// # Errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If there are remaining members in the object a [`ReaderError::UnexpectedStructure`] is returned.
    /// [`skip_name`](Self::skip_name) and [`skip_value`](Self::skip_value) can be used to skip these
    /// remaining members in case they should be ignored:
    /// ```
    /// # use ron::reader::*;
    /// # let mut json_reader = JsonStreamReader::new("{}".as_bytes());
    /// # json_reader.begin_object()?;
    /// while json_reader.has_next()? {
    ///     // Skip member name
    ///     json_reader.skip_name()?;
    ///     // Skip member value
    ///     json_reader.skip_value()?;
    /// }
    ///
    /// json_reader.end_object()?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON reader which is currently not inside a JSON object,
    /// or when the value of a member is currently expected. Both cases indicate incorrect
    /// usage by the user and are unrelated to the JSON data.
    fn end_object(&mut self) -> Result<(), ReaderError>;

    /// Begins consuming a JSON array
    ///
    /// The method [`has_next`](Self::has_next) can be used to check if there is a next array item. To consume an item one of
    /// the regular value reading methods such as [`next_number`](Self::next_number) can be used. At the end call
    /// [`end_array`](Self::end_array) to consume the closing bracket of the JSON array.
    ///
    /// Note that JSON arrays can contain values of different types, so for example the
    /// following is valid JSON: `[1, true, "a"]`
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// let mut json_reader = JsonStreamReader::new("[1, 2, 3]".as_bytes());
    /// json_reader.begin_array()?;
    ///
    /// // Prints: "Number: 1", "Number: 2", "Number: 3"
    /// while json_reader.has_next()? {
    ///     let number: u32 = json_reader.next_number()??;
    ///     println!("Number: {number}");
    /// }
    ///
    /// json_reader.end_array()?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If there is no next value a [`ReaderError::UnexpectedStructure`] is returned. The [`has_next`](Self::has_next)
    /// method can be used to check if there is a next value.
    ///
    /// If the next value is not a JSON array but is a value of a different type
    /// a [`ReaderError::UnexpectedValueType`] is returned. The [`peek`](Self::peek) method can be used to
    /// check the type if it is not known in advance.
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently expects a member name, or
    /// when called after the top-level value has already been consumed and multiple top-level
    /// values are not enabled in the [`ReaderSettings`]. Both cases indicate incorrect
    /// usage by the user and are unrelated to the JSON data.
    fn begin_array(&mut self) -> Result<(), ReaderError>;

    /// Consumes the closing bracket `]` of the current JSON array
    ///
    /// This method is used to end a JSON array started by [`begin_array`](Self::begin_array).
    ///
    /// # Errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If there are remaining items in the array a [`ReaderError::UnexpectedStructure`] is returned.
    /// [`skip_value`](Self::skip_value) can be used to skip these remaining items in case they should be ignored:
    /// ```
    /// # use ron::reader::*;
    /// # let mut json_reader = JsonStreamReader::new("[]".as_bytes());
    /// # json_reader.begin_array()?;
    /// while json_reader.has_next()? {
    ///     json_reader.skip_value()?;
    /// }
    ///
    /// json_reader.end_array()?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON reader which is currently not inside a JSON array. This
    /// indicates incorrect usage by the user and is unrelated to the JSON data.
    fn end_array(&mut self) -> Result<(), ReaderError>;

    /// Checks if there is a next element in the current JSON array or object, without consuming it
    ///
    /// Returns `true` if there is a next element, `false` otherwise. When multiple top-level
    /// values are allowed by the [`ReaderSettings`] this method can also be used to check if
    /// there are more top-level values.
    ///
    /// This method can be useful as condition of a `while` loop when processing a JSON array or object
    /// of unknown size.
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// let mut json_reader = JsonStreamReader::new("[1]".as_bytes());
    /// json_reader.begin_array()?;
    ///
    /// // Array has a next item
    /// assert!(json_reader.has_next()?);
    ///
    /// json_reader.skip_value()?;
    /// // Array does not have a next item anymore
    /// assert_eq!(false, json_reader.has_next()?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently expects a member name, or
    /// when called after the top-level value has already been consumed and multiple top-level
    /// values are not enabled in the [`ReaderSettings`]. Both cases indicate incorrect
    /// usage by the user and are unrelated to the JSON data.
    ///
    /// Additionally this method also panics when called on a JSON reader which has not
    /// consumed any top-level value yet. An empty JSON document is not valid so there
    /// should be no need to check for a next element since there must always be one.
    fn has_next(&mut self) -> Result<bool, ReaderError>;

    /// Consumes and returns the name of the next JSON object member
    ///
    /// Afterwards one of the value reading methods such as [`next_number`](Self::next_number) can be
    /// used to read the corresponding member value.
    ///
    /// **Important:** This method does not detect duplicate  member names, such as
    /// in `{"a": 1, "a": 2}`. Programs processing JSON data from an untrusted source
    /// must implement this detection themselves to protect against exploits relying
    /// on different handling of duplicate names by different JSON parsing libraries.
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// let mut json_reader = JsonStreamReader::new(r#"{"a": 1}"#.as_bytes());
    /// json_reader.begin_object()?;
    /// assert_eq!("a", json_reader.next_name()?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If there is no next object member a [`ReaderError::UnexpectedStructure`] is returned.
    /// [`has_next`](Self::has_next) can be used to check if there are further members in the current JSON object.
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently does not expect a member name. This
    /// indicates incorrect usage by the user and is unrelated to the JSON data.
    fn next_name(&mut self) -> Result<String, ReaderError>;

    /// Consumes and returns a JSON string value
    ///
    /// This method is only intended to consume string values, it cannot be used to consume
    /// JSON object member names. The method [`next_name`](Self::next_name) has to be used for that.
    ///
    /// To avoid reading the complete string value into memory, the method [`next_string_reader`](Self::next_string_reader)
    /// can be used to obtain a reader which allows lazily reading the value. Especially for
    /// large string values this can be useful.
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// let mut json_reader = JsonStreamReader::new(r#""text with \"quotes\"""#.as_bytes());
    /// assert_eq!("text with \"quotes\"", json_reader.next_string()?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If there is no next value a [`ReaderError::UnexpectedStructure`] is returned. The [`has_next`](Self::has_next)
    /// method can be used to check if there is a next value.
    ///
    /// If the next value is not a JSON string value but is a value of a different type
    /// a [`ReaderError::UnexpectedValueType`] is returned. The [`peek`](Self::peek) method can be used to
    /// check the type if it is not known in advance.
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently expects a member name, or
    /// when called after the top-level value has already been consumed and multiple top-level
    /// values are not enabled in the [`ReaderSettings`]. Both cases indicate incorrect
    /// usage by the user and are unrelated to the JSON data.
    fn next_string(&mut self) -> Result<String, ReaderError>;

    /// Provides a reader for lazily reading a JSON string value
    ///
    /// This method is mainly designed to process large string values in a memory efficient
    /// way. If that is not a concern the method [`next_string`](Self::next_string) should be used instead.
    ///
    /// This method is only intended to consume string values, it cannot be used to consume
    /// JSON object member names. The method [`next_name`](Self::next_name) has to be used for that.
    ///
    /// JSON syntax errors which occur while consuming the JSON document with the reader
    /// are reported as [`std::io::Error`] for that reader.
    ///
    /// **Important:** The data of the string value reader must be fully consumed, that means
    /// `read` has to be called with a non-empty buffer until it returns `Ok(0)`. Otherwise the
    /// string value reader will still be considered 'active' and all methods of this JSON reader
    /// will panic. Note that after finishing reading from the string value reader, it might be
    /// necessary to explicitly `drop(...)` it for the Rust compiler to allow using the original
    /// JSON reader again.
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// let mut json_reader = JsonStreamReader::new(r#"["hello"]"#.as_bytes());
    /// json_reader.begin_array()?;
    ///
    /// let mut string_reader = json_reader.next_string_reader()?;
    /// let mut buf = [0; 1];
    ///
    /// // Important: This calls read until it returns Ok(0) to properly end the string value
    /// while string_reader.read(&mut buf)? > 0 {
    ///     println!("Read byte: {}", buf[0]);
    /// }
    ///
    /// // Drop the string reader to allow using the JSON reader again
    /// drop(string_reader);
    ///
    /// json_reader.end_array()?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If there is no next value a [`ReaderError::UnexpectedStructure`] is returned. The [`has_next`](Self::has_next)
    /// method can be used to check if there is a next value.
    ///
    /// If the next value is not a JSON string value but is a value of a different type
    /// a [`ReaderError::UnexpectedValueType`] is returned. The [`peek`](Self::peek) method can be used to
    /// check the type if it is not known in advance.
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently expects a member name, or
    /// when called after the top-level value has already been consumed and multiple top-level
    /// values are not enabled in the [`ReaderSettings`]. Both cases indicate incorrect
    /// usage by the user and are unrelated to the JSON data.
    fn next_string_reader(&mut self) -> Result<Box<dyn Read + '_>, ReaderError>;

    /// Consumes and returns a JSON number value
    ///
    /// The result is either the parsed number or the parse error. It might be necessary to
    /// help the Rust compiler a bit by explicitly specifying the number type in case it cannot
    /// be inferred automatically.
    ///
    /// If parsing the number should be deferred to a later point or the exact format of the
    /// JSON number should be preserved, the method [`next_number_as_string`](Self::next_number_as_string) can be used.
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// let mut json_reader = JsonStreamReader::new("12".as_bytes());
    /// assert_eq!(12_u32, json_reader.next_number()??);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If there is no next value a [`ReaderError::UnexpectedStructure`] is returned. The [`has_next`](Self::has_next)
    /// method can be used to check if there is a next value.
    ///
    /// If the next value is not a JSON number value but is a value of a different type
    /// a [`ReaderError::UnexpectedValueType`] is returned. The [`peek`](Self::peek) method can be used to
    /// check the type if it is not known in advance.
    ///
    /// If the number is too large or has too many decimal places a [`ReaderError::UnsupportedNumberValue`]
    /// is returned, depending on the [reader settings](ReaderSettings::restrict_number_values).
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently expects a member name, or
    /// when called after the top-level value has already been consumed and multiple top-level
    /// values are not enabled in the [`ReaderSettings`]. Both cases indicate incorrect
    /// usage by the user and are unrelated to the JSON data.
    /*
     * TODO: Maybe restrict FromStr somehow to numbers?
     * TODO: Solve this in a cleaner way than Result<Result<...>, ...>?
     */
    fn next_number<T: FromStr>(&mut self) -> Result<Result<T, T::Err>, ReaderError>;

    /// Consumes and returns the string representation of a JSON number value
    ///
    /// This method is mainly intended for situations where parsing the number should be
    /// deferred to a later point, or the exact format of the JSON number should be preserved.
    /// However, this method nonetheless validates the JSON number matches the format
    /// described by the JSON specification.
    ///
    /// The method [`next_number`](Self::next_number) can be used instead to parse the number directly in place.
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// let mut json_reader = JsonStreamReader::new("12.0e5".as_bytes());
    /// assert_eq!("12.0e5", json_reader.next_number_as_string()?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If there is no next value a [`ReaderError::UnexpectedStructure`] is returned. The [`has_next`](Self::has_next)
    /// method can be used to check if there is a next value.
    ///
    /// If the next value is not a JSON number value but is a value of a different type
    /// a [`ReaderError::UnexpectedValueType`] is returned. The [`peek`](Self::peek) method can be used to
    /// check the type if it is not known in advance.
    ///
    /// If the number is too large or has too many decimal places a [`ReaderError::UnsupportedNumberValue`]
    /// is returned, depending on the [reader settings](ReaderSettings::restrict_number_values).
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently expects a member name, or
    /// when called after the top-level value has already been consumed and multiple top-level
    /// values are not enabled in the [`ReaderSettings`]. Both cases indicate incorrect
    /// usage by the user and are unrelated to the JSON data.
    fn next_number_as_string(&mut self) -> Result<String, ReaderError>;

    /// Consumes and returns a JSON boolean value
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// let mut json_reader = JsonStreamReader::new("true".as_bytes());
    /// assert_eq!(true, json_reader.next_bool()?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If there is no next value a [`ReaderError::UnexpectedStructure`] is returned. The [`has_next`](Self::has_next)
    /// method can be used to check if there is a next value.
    ///
    /// If the next value is not a JSON boolean value but is a value of a different type
    /// a [`ReaderError::UnexpectedValueType`] is returned. The [`peek`](Self::peek) method can be used to
    /// check the type if it is not known in advance.
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently expects a member name, or
    /// when called after the top-level value has already been consumed and multiple top-level
    /// values are not enabled in the [`ReaderSettings`]. Both cases indicate incorrect
    /// usage by the user and are unrelated to the JSON data.
    fn next_bool(&mut self) -> Result<bool, ReaderError>;

    /// Consumes a JSON null value
    ///
    /// This method does not return a value since there is nothing meaningful to return.
    /// Either the JSON value is a JSON null, or otherwise an error is returned because the
    /// value had a different type (see "Errors" section below).
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// let mut json_reader = JsonStreamReader::new("null".as_bytes());
    /// json_reader.next_null()?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If there is no next value a [`ReaderError::UnexpectedStructure`] is returned. The [`has_next`](Self::has_next)
    /// method can be used to check if there is a next value.
    ///
    /// If the next value is not a JSON null value but is a value of a different type
    /// a [`ReaderError::UnexpectedValueType`] is returned. The [`peek`](Self::peek) method can be used to
    /// check the type if it is not known in advance.
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently expects a member name, or
    /// when called after the top-level value has already been consumed and multiple top-level
    /// values are not enabled in the [`ReaderSettings`]. Both cases indicate incorrect
    /// usage by the user and are unrelated to the JSON data.
    fn next_null(&mut self) -> Result<(), ReaderError>;

    /// Deserializes a Serde [`Deserialize`](serde::de::Deserialize) from the next value
    ///
    /// This method is part of the optional Serde integration feature, see the
    /// [`serde`](crate::serde) module of this crate for more information.
    ///
    /// If it is not possible to directly deserialize a value in place, instead of using
    /// this method a [`JsonReaderDeserializer`](crate::serde::JsonReaderDeserializer)
    /// can be constructed and deserialization can be performed using it later on. However,
    /// this should only be rarely necessary.
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// # use ron::reader::json_path::*;
    /// # use serde::*;
    /// // In this example JSON data comes from a string;
    /// // normally it would come from a file or a network connection
    /// let json = r#"{"outer": {"text": "some text", "number": 5}}"#;
    /// let mut json_reader = JsonStreamReader::new(json.as_bytes());
    ///
    /// // Skip outer data using the regular JsonReader methods
    /// json_reader.seek_to(&json_path!["outer"])?;
    ///
    /// #[derive(Deserialize, PartialEq, Debug)]
    /// struct MyStruct {
    ///     text: String,
    ///     number: u64,
    /// }
    ///
    /// let value: MyStruct = json_reader.deserialize_next()?;
    ///
    /// // Skip the remainder of the JSON document
    /// json_reader.skip_to_top_level()?;
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
    /// # Security
    /// Since JSON data can have an arbitrary structure and can contain arbitrary
    /// data, care must be taken when processing untrusted data. See the documentation
    /// of [`JsonReaderDeserializer`](crate::serde::JsonReaderDeserializer) for
    /// security considerations.
    ///
    /// # Errors
    /// Errors can occur when either this JSON reader or the `Deserialize` encounters an
    /// error. In which situations this can happen depends on the `Deserialize` implementation.
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently expects a member name, or
    /// when called after the top-level value has already been consumed and multiple top-level
    /// values are not enabled in the [`ReaderSettings`]. Both cases indicate incorrect
    /// usage by the user and are unrelated to the JSON data.
    #[cfg(feature = "serde")]
    fn deserialize_next<'de, D: serde::de::Deserialize<'de>>(
        &mut self,
    ) -> Result<D, crate::serde::DeserializerError>;

    /// Skips the name of the next JSON object member
    ///
    /// Afterwards one of the value reading methods such as [`next_number`](Self::next_number) can be
    /// used to read the corresponding member value.
    ///
    /// Skipping member names can be useful when the only the values of the JSON object members are
    /// relevant for the application processing the JSON document but the member names don't matter.
    ///
    /// Skipping member names with this method is usually more efficient than calling [`next_name`](Self::next_name)
    /// but discarding its result. However, `skip_name` nonetheless also verifies that the skipped
    /// name has valid syntax.
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// let mut json_reader = JsonStreamReader::new(r#"{"a": 1}"#.as_bytes());
    /// json_reader.begin_object()?;
    ///
    /// // Skip member name "a"
    /// json_reader.skip_name()?;
    ///
    /// assert_eq!("1", json_reader.next_number_as_string()?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// To skip to a specific location in the JSON document the method [`seek_to`](Self::seek_to) can be used.
    ///
    /// # Errors
    /// None, besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`].
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently does not expect a member name. This
    /// indicates incorrect usage by the user and is unrelated to the JSON data.
    fn skip_name(&mut self) -> Result<(), ReaderError>;

    /// Skips the next value
    ///
    /// This method can be used to skip top-level values, JSON array items and JSON object member
    /// values. To skip an object member name, the method [`skip_name`](Self::skip_name) has to be used.  
    /// Skipping a JSON array or object skips the complete value including all nested ones, if any.
    ///
    /// Skipping values can be useful when parts of the processed JSON document are not relevant
    /// for the application processing it.
    ///
    /// Skipping values with this method is usually more efficient than calling regular value reading
    /// methods (such as `next_string()`) but discarding their result.
    /// However, `skip_value` nonetheless also verifies that the skipped JSON data has valid syntax.
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// let mut json_reader = JsonStreamReader::new(r#"{"a": [{}], "b": 1}"#.as_bytes());
    /// json_reader.begin_object()?;
    ///
    /// assert_eq!("a", json_reader.next_name()?);
    ///
    /// // Skip member value [{}]
    /// json_reader.skip_value()?;
    ///
    /// assert_eq!("b", json_reader.next_name()?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// To skip to a specific location in the JSON document the method [`seek_to`](Self::seek_to) can be used.
    ///
    /// # Errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If there is no next value a [`ReaderError::UnexpectedStructure`] is returned. The [`has_next`](Self::has_next)
    /// method can be used to check if there is a next value.
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently expects a member name ([`skip_name`](Self::skip_name)
    /// has to be used for that), or when called after the top-level value has already been consumed
    /// and multiple top-level values are not enabled in the [`ReaderSettings`]. Both cases indicate
    /// incorrect usage by the user and are unrelated to the JSON data.
    fn skip_value(&mut self) -> Result<(), ReaderError>;

    /// Seeks to the specified location in the JSON document
    ///
    /// Seeks to the specified relative JSONPath in the JSON document by skipping all previous
    /// values. The JSON reader is expected to be positioned before the first value specified
    /// in the path. Once this method returns successfully the reader will be positioned
    /// before the last element specified by the path.
    ///
    /// For example for the JSONPath `foo[2]` it will start consuming a JSON object, skipping members
    /// until it finds one with name "foo". Then it starts consuming the member value, expecting that
    /// it is a JSON array, until right before the array item with (starting at 0) index 2.
    /// If multiple members in a JSON object have the same name (for example `{"a": 1, "a": 2}`)
    /// this method will seek to the first occurrence.
    ///
    /// Seeking to a specific location can be useful when parts of the processed JSON document
    /// are not relevant for the application processing it.
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// # use ron::reader::json_path::*;
    /// let mut json_reader = JsonStreamReader::new(
    ///     r#"{"bar": true, "foo": ["a", "b", "c"]}"#.as_bytes()
    /// );
    /// json_reader.seek_to(&json_path!["foo", 2])?;
    ///
    /// // Can now consume the value to which the call seeked to
    /// assert_eq!("c", json_reader.next_string()?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If the structure or the value types of the JSON document do not match the structure expected
    /// by the JSONPath, either a [`ReaderError::UnexpectedStructure`] or a [`ReaderError::UnexpectedValueType`]
    /// is returned.
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently expects a member name, or
    /// when called after the top-level value has already been consumed and multiple top-level
    /// values are not enabled in the [`ReaderSettings`]. Both cases indicate incorrect
    /// usage by the user and are unrelated to the JSON data.
    /*
     * TODO: Should this rather take a `IntoIterator<Item = JsonPathPiece>` as path?
     *   Though use cases where the path is created dynamically and is not present as slice might be rare
     *   When changing this method, might render the `JsonPath` type alias a bit pointless then
     */
    fn seek_to(&mut self, rel_json_path: &JsonPath) -> Result<(), ReaderError>;

    /// Skips the remaining elements of all currently enclosing JSON arrays and objects
    ///
    /// Based on the current JSON reader position skips the remaining elements of all enclosing
    /// JSON arrays and objects (if any) until the top-level is reached. That is, for every array
    /// started with [`begin_array`](Self::begin_array) and for every object started with [`begin_object`](Self::begin_object)
    /// the remaining elements are skipped and the end of the array respectively object is consumed.
    /// During skipping, the syntax of the skipped values is validated. Calling this method has no
    /// effect when there is currently no enclosing JSON array or object.
    ///
    /// This method is useful when a subsection of a JSON document has been consumed, for example
    /// with the help of [`seek_to`](Self::seek_to), and afterwards either
    /// - the syntax of the remainder of the document should be validated and trailing data should
    ///   be rejected, by calling [`consume_trailing_whitespace`](Self::consume_trailing_whitespace)
    /// - or, multiple top-level values are enabled in the [`ReaderSettings`] and the next top-level
    ///   value should be consumed
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// # use ron::reader::json_path::*;
    /// let mut json_reader = JsonStreamReader::new(
    ///     r#"{"bar": true, "foo": ["a", "b", "c"]}"#.as_bytes()
    /// );
    /// json_reader.seek_to(&json_path!["foo", 2])?;
    ///
    /// // Consume the value to which the call seeked to
    /// assert_eq!("c", json_reader.next_string()?);
    ///
    /// // Skip the remainder of the document
    /// json_reader.skip_to_top_level()?;
    /// // And verify that there is only optional whitespace, but no trailing data
    /// json_reader.consume_trailing_whitespace()?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// None, besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`].
    fn skip_to_top_level(&mut self) -> Result<(), ReaderError>;

    /// Consumes the next value and writes it to the given JSON writer
    ///
    /// This method consumes the next value and calls the corresponding methods on the
    /// JSON writer to emit the value again. Due to this, whitespace and comments, if enabled
    /// in the [`ReaderSettings`], are not preserved. Instead the formatting of the output
    /// is dependent on the configuration of the JSON writer. Similarly the Unicode characters
    /// of member names and string values might be escaped differently. However, all these differences
    /// don't have an effect on the JSON value. JSON readers will consider it to be equivalent.
    /// For JSON numbers the exact format is preserved.
    ///
    /// This method is useful for extracting a subsection from a JSON document and / or for
    /// embedding it into another JSON document. Extraction can be done by using for example
    /// [`seek_to`](Self::seek_to) to position the reader before calling this method. Embedding
    /// can be done by already writing JSON data to the JSON writer before calling this method.
    ///
    /// # Examples
    /// ```
    /// # use ron::reader::*;
    /// # use ron::reader::json_path::*;
    /// # use ron::writer::*;
    /// let mut json_reader = JsonStreamReader::new(
    ///     r#"{"bar": true, "foo": [1, 2]}"#.as_bytes()
    /// );
    /// json_reader.seek_to(&json_path!["foo"])?;
    ///
    /// let mut writer = Vec::<u8>::new();
    /// let mut json_writer = JsonStreamWriter::new(&mut writer);
    /// json_writer.begin_object()?;
    /// json_writer.name("embedded")?;
    ///
    /// // Extract subsection from reader and embed it in the document created by the writer
    /// json_reader.transfer_to(&mut json_writer)?;
    ///
    /// json_writer.end_object()?;
    /// json_writer.finish_document()?;
    ///
    /// assert_eq!(r#"{"embedded":[1,2]}"#, std::str::from_utf8(&writer)?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// Errors are reported as [`TransferError`] which wraps either an error which occurred for this
    /// JSON reader or an error which occurred for the given JSON writer.
    ///
    /// ## Reader errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If there is no next value a [`ReaderError::UnexpectedStructure`] is returned. The [`has_next`](Self::has_next)
    /// method can be used to check if there is a next value.
    ///
    /// ## Writer errors
    /// If writing the JSON value fails an IO error is returned.
    ///
    /// # Panics
    /// Panics when called on a JSON reader which currently expects a member name, or
    /// when called after the top-level value has already been consumed and multiple top-level
    /// values are not enabled in the [`ReaderSettings`].
    ///
    /// Panics when the given JSON writer currently expects a member name, or when it has already
    /// written a top-level value and multiple top-level values are not enabled in the
    /// [`WriterSettings`]($crate::writer::WriterSettings).
    ///
    /// These cases indicate incorrect usage by the user and are unrelated to the JSON data.
    /*
     * TODO: Choose a different name which makes it clearer that only the next value is transferred, e.g. `transfer_next_to`?
     * TODO: Are the use cases common enough to justify the existence of this method?
     */
    fn transfer_to<W: JsonWriter>(&mut self, json_writer: &mut W) -> Result<(), TransferError>;

    /// Consumes trailing whitespace at the end of the top-level value
    ///
    /// Additionally, if comments are allowed by the [`ReaderSettings`] also consumes trailing comments.
    /// If there is any trailing data a [`ReaderError::SyntaxError`] is returned.
    ///
    /// This method can be useful to verify that a JSON document is wellformed and does not
    /// have any unexpected data at the end. This is not checked automatically by this JSON reader.
    ///
    /// When multiple top-level values are allowed by the [`ReaderSettings`] but not all
    /// top-level values are relevant they can be skipped with of loop calling [`has_next`](Self::has_next) and [`skip_value`](Self::skip_value)
    /// to allow calling `consume_trailing_whitespace` eventually:
    /// ```
    /// # use ron::reader::*;
    /// # let mut json_reader = JsonStreamReader::new_custom("1".as_bytes(), ReaderSettings { allow_multiple_top_level: true, ..ReaderSettings::default() });
    /// # json_reader.skip_value()?;
    /// // Skip all remaining top-level values
    /// while json_reader.has_next()? {
    ///     json_reader.skip_value()?;
    /// }
    ///
    /// // Verify that there is only optional whitespace, but no trailing data
    /// json_reader.consume_trailing_whitespace()?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// **Important:** It is expected that there is always at least one top-level value
    /// in a JSON document, so calling this method without having consumed a value yet
    /// will panic, see "Panics" section below.
    ///
    /// # Errors
    /// (besides [`ReaderError::IoError`])
    ///
    /// If there is trailing data at the end of the top-level value a [`ReaderError::SyntaxError`]
    /// of kind [`SyntaxErrorKind::TrailingData`] is returned.
    ///
    /// # Panics
    /// Panics when called on a JSON reader which has not read any top-level yet, or when
    /// called while the top-level value has not been fully consumed yet. Both cases
    /// indicate incorrect usage by the user and are unrelated to the JSON data.
    /* Consumes 'self' */
    fn consume_trailing_whitespace(self) -> Result<(), ReaderError>;
}

#[derive(PartialEq, Clone, Copy, strum_macros::Display, Debug)]
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
enum StringReadingError {
    #[error("syntax error: {0}")]
    SyntaxError(#[from] JsonSyntaxError),
    #[error("IO error: {0}")]
    IoError(#[from] IoError),
}

impl From<StringReadingError> for ReaderError {
    fn from(e: StringReadingError) -> Self {
        match e {
            StringReadingError::SyntaxError(e) => ReaderError::SyntaxError(e),
            StringReadingError::IoError(e) => ReaderError::IoError(e),
        }
    }
}

#[derive(PartialEq, Debug)]
enum StackValue {
    Array,
    Object,
}

const READER_BUF_SIZE: usize = 1024;

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
///   does not use recrusive calls, users of this reader must make sure to not use recursive calls
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
    buf: [u8; READER_BUF_SIZE],
    buf_pos: usize,
    /// Index (exclusive) up to which [`buf`](Self::buf) is filled
    buf_end_pos: usize,
    reached_eof: bool,

    peeked: Option<PeekedValue>,
    /// Whether the current array or object is empty, or at top-level whether
    /// at least one value has been consumed already
    is_empty: bool,
    expects_member_name: bool,
    stack: Vec<StackValue>,
    is_string_value_reader_active: bool,

    line: u32,
    column: u32,
    json_path: Vec<JsonPathPiece>,

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
            .field("json_path", &self.json_path)
            .field("reader_settings", &self.reader_settings)
            .finish()
    }
}

// 4 (max bytes for UTF-8 encoded char) - 1, since at least one byte was already consumed
const STRING_VALUE_READER_BUF_SIZE: usize = 3;

struct StringValueReader<'j, R: Read> {
    json_reader: &'j mut JsonStreamReader<R>,
    /// Buffer in case multi-byte character is read but caller did not provide large enough buffer
    utf8_buf: [u8; STRING_VALUE_READER_BUF_SIZE],
    /// Start position within [utf8_buf]
    utf8_start_pos: usize,
    /// Number of bytes currently in the [utf8_buf]
    utf8_count: usize,
    reached_end: bool,
}

/// Settings to customize the JSON reader behavior
///
/// These settings are used by [`JsonStreamReader::new_custom`]. To avoid repeating the
/// default values for unchanged settings `..Default::default()` can be used:
/// ```
/// # use ron::reader::ReaderSettings;
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
    /// - end of line comments: `// ...`  
    ///   The comment spans to the end of the line (next `\r\n`, `\r` or `\n`)
    /// - block comments: `/* ... */`  
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
    pub allow_multiple_top_level: bool,

    /// Whether to update the error location path while skipping values
    ///
    /// When enabled, skipping JSON arrays and objects with methods such as [`JsonReader::skip_value`] or
    /// [`JsonReader::seek_to`] will update the path which is reported for [error locations](JsonErrorLocation::path).
    /// However, updating the path incurs overhead because JSON object member names cannot be skipped in
    /// an efficient way but must be read to be available for the path information.  
    /// When disabled the path is not updated which increases performance but in case of syntax errors might
    /// make them more difficult to identify. [Line](JsonErrorLocation::line) and [column](JsonErrorLocation::column)
    /// numbers are however not affected and will always be accurate.
    ///
    /// This setting has no effect on the JSON parsing behavior, it only affects the information included
    /// for errors.
    pub update_path_during_skip: bool,

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
    /// - update path during skip: enabled
    /// - restrict number values: enabled
    ///
    /// These defaults are compliant with the JSON specification.
    fn default() -> Self {
        ReaderSettings {
            allow_comments: false,
            allow_trailing_comma: false,
            allow_multiple_top_level: false,
            update_path_during_skip: true,
            restrict_number_values: true,
        }
    }
}

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
        Self {
            reader,
            buf: [0; READER_BUF_SIZE],
            buf_pos: 0,
            buf_end_pos: 0,
            reached_eof: false,
            peeked: None,
            is_empty: true,
            expects_member_name: false,
            stack: Vec::new(),
            is_string_value_reader_active: false,
            line: 0,
            column: 0,
            json_path: Vec::new(),
            reader_settings,
        }
    }

    fn create_error_location(&self) -> JsonErrorLocation {
        JsonErrorLocation {
            path: format_abs_json_path(&self.json_path),
            line: self.line,
            column: self.column,
        }
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

    fn ensure_non_empty_buffer(&mut self) -> Result<bool, IoError> {
        if self.reached_eof {
            return Ok(false);
        }
        if self.buf_pos < self.buf_end_pos {
            return Ok(true);
        }

        self.buf_pos = 0;
        self.buf_end_pos = self.reader.read(&mut self.buf)?;
        if self.buf_end_pos == 0 {
            self.reached_eof = true;
            Ok(false)
        } else {
            Ok(true)
        }
    }

    fn peek_byte(&mut self) -> Result<Option<u8>, IoError> {
        if self.ensure_non_empty_buffer()? {
            Ok(Some(self.buf[self.buf_pos]))
        } else {
            Ok(None)
        }
    }

    fn skip_peeked_byte(&mut self) {
        debug_assert!(self.buf_pos < self.buf_end_pos);
        self.buf_pos += 1;
    }

    fn read_byte(&mut self, eof_error_kind: SyntaxErrorKind) -> Result<u8, StringReadingError> {
        if self.ensure_non_empty_buffer()? {
            let b = self.buf[self.buf_pos];
            self.buf_pos += 1;
            Ok(b)
        } else {
            Err(JsonSyntaxError {
                kind: eof_error_kind,
                location: self.create_error_location(),
            })?
        }
    }

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

            match byte {
                b'\n' => {
                    self.skip_peeked_byte();

                    // Only count \r\n as one line break
                    if !has_cr {
                        self.column = 0;
                        self.line += 1;
                    }
                }
                b'\r' => {
                    self.skip_peeked_byte();
                    self.column = 0;
                    self.line += 1;
                }
                // Skip ASCII character
                0x00..=0x7F => {
                    self.skip_peeked_byte();
                    self.column += 1;
                }
                _ => {
                    self.skip_peeked_byte();
                    // Validate the UTF-8 data, but ignore it
                    self.read_utf8_bytes(byte, &mut |_| {})
                        .map_err(ReaderError::from)?;
                    self.column += 1;
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

                match self.read_byte(SyntaxErrorKind::IncompleteComment)? {
                    b'*' => {
                        self.column += 1;
                        self.skip_to_block_comment_end()?;
                    }
                    b'/' => {
                        self.column += 1;
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

        // Note: Don't adjust self.column yet, is done when peeked value is actually consumed
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

        let byte = self.skip_whitespace(None)?;
        if byte.is_none() {
            return Ok(None);
        }
        let mut byte = byte.unwrap();

        let mut has_trailing_comma = false;
        let mut comma_column = 0;
        let can_have_comma = !self.is_empty && (self.is_in_array() || self.expects_member_name);

        if byte == b',' {
            if !can_have_comma {
                return self.create_syntax_value_error(SyntaxErrorKind::UnexpectedComma);
            }
            self.skip_peeked_byte();
            comma_column = self.column;
            self.column += 1;
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
                self.column = comma_column; // report location of comma
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
    }

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
        self.json_path.pop();

        // Clear expects_member_name in case current container is now an array; on_value_end() call
        // below will set expects_member_name again if current container is an object
        self.expects_member_name = false;

        self.on_value_end();
    }

    fn on_value_end(&mut self) {
        // Update array path
        if self.is_in_array() {
            match self.json_path.last_mut().unwrap() {
                JsonPathPiece::ArrayItem(index) => *index += 1,
                _ => unreachable!("Path should be array item"),
            }
        }

        // After value was consumed indicate that object member name is expected next
        if self.is_in_object() {
            self.expects_member_name = true;
        }

        // Enclosing container is not empty since this method call here is processing its child
        self.is_empty = false;
    }

    fn read_unicode_escape_hex_digit(&mut self) -> Result<u32, StringReadingError> {
        let byte = self.read_byte(SyntaxErrorKind::MalformedEscapeSequence)?;
        match byte {
            b'0'..=b'9' => Ok(u32::from(byte - b'0')),
            b'a'..=b'f' => Ok(u32::from(byte - b'a' + 10)),
            b'A'..=b'F' => Ok(u32::from(byte - b'A' + 10)),
            _ => Err(JsonSyntaxError {
                kind: SyntaxErrorKind::MalformedEscapeSequence,
                location: self.create_error_location(),
            })?,
        }
    }

    fn read_unicode_escape(&mut self) -> Result<u32, StringReadingError> {
        let d1 = self.read_unicode_escape_hex_digit()?;
        let d2 = self.read_unicode_escape_hex_digit()?;
        let d3 = self.read_unicode_escape_hex_digit()?;
        let d4 = self.read_unicode_escape_hex_digit()?;

        Ok(d4 | d3 << 4 | d2 << 8 | d1 << 12)
    }

    fn read_utf8_bytes<C: FnMut(u8)>(
        &mut self,
        byte1: u8,
        consumer: &mut C,
    ) -> Result<(), StringReadingError> {
        fn invalid_utf8_err() -> Result<(), StringReadingError> {
            Err(StringReadingError::IoError(IoError::new(
                ErrorKind::InvalidData,
                "invalid UTF-8 data",
            )))
        }

        let byte2 = self.read_byte(SyntaxErrorKind::IncompleteDocument)?;

        if (byte2 & 0b1100_0000) != 0b1000_0000 {
            return invalid_utf8_err();
        }

        if (byte1 & 0b1110_0000) == 0b1100_0000 {
            let code_point =
                (u32::from(byte1) & !0b1110_0000) << 6 | (u32::from(byte2) & !0b1100_0000);
            // Check for 'overlong encoding'
            if code_point < 0x80 {
                return invalid_utf8_err();
            }
            consumer(byte1);
            consumer(byte2);
        } else {
            let byte3 = self.read_byte(SyntaxErrorKind::IncompleteDocument)?;

            if (byte3 & 0b1100_0000) != 0b1000_0000 {
                return invalid_utf8_err();
            }

            if (byte1 & 0b1111_0000) == 0b1110_0000 {
                let code_point = (u32::from(byte1) & !0b1111_0000) << 12
                    | (u32::from(byte2) & !0b1100_0000) << 6
                    | (u32::from(byte3) & !0b1100_0000);
                // Check for 'overlong encoding', or for UTF-16 surrogate chars encoded in UTF-8
                if code_point < 0x800 || (0xD800..=0xDFFF).contains(&code_point) {
                    return invalid_utf8_err();
                }

                consumer(byte1);
                consumer(byte2);
                consumer(byte3);
            } else if (byte1 & 0b1111_1000) == 0b1111_0000 {
                let byte4 = self.read_byte(SyntaxErrorKind::IncompleteDocument)?;
                if (byte4 & 0b1100_0000) == 0b1000_0000 {
                    let code_point = (u32::from(byte1) & !0b1111_1000) << 18
                        | (u32::from(byte2) & !0b1100_0000) << 12
                        | (u32::from(byte3) & !0b1100_0000) << 6
                        | (u32::from(byte4) & !0b1100_0000);

                    // Check for 'overlong encoding', or encoding of invalid code point
                    if !(0x10000..=0x10FFFF).contains(&code_point) {
                        return invalid_utf8_err();
                    }

                    consumer(byte1);
                    consumer(byte2);
                    consumer(byte3);
                    consumer(byte4);
                } else {
                    return invalid_utf8_err();
                }
            } else {
                return invalid_utf8_err();
            }
        }
        Ok(())
    }

    fn read_unicode_escape_char(&mut self) -> Result<char, StringReadingError> {
        let mut c = self.read_unicode_escape()?;
        let mut consumed_chars_count = 4;

        // Unpaired low surrogate
        if (0xDC00..=0xDFFF).contains(&c) {
            return Err(JsonSyntaxError {
                kind: SyntaxErrorKind::UnpairedSurrogatePairEscapeSequence,
                location: self.create_error_location(),
            })?;
        }
        // If char is high surrogate, expect unicode escaped low surrogate
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

        self.column += consumed_chars_count;
        // unwrap() here should be safe since checks above made sure this is a valid Rust `char`
        Ok(char::from_u32(c).unwrap())
    }

    /// Reads the next character of a member name or string value
    ///
    /// If it is an unescaped `"` returns true. Otherwise passes the bytes of the char
    /// (1 - 4 bytes) to the given consumer and returns false.
    fn read_string_bytes<C: FnMut(u8)>(
        &mut self,
        consumer: &mut C,
    ) -> Result<bool, StringReadingError> {
        let byte = self.read_byte(SyntaxErrorKind::IncompleteDocument)?;

        let mut consumed_chars_count = 1;
        match byte {
            // Read escape sequence
            b'\\' => {
                let byte = self.read_byte(SyntaxErrorKind::MalformedEscapeSequence)?;
                consumed_chars_count += 1;

                match byte {
                    b'"' | b'\\' | b'/' => consumer(byte),
                    b'b' => consumer(0x08),
                    b'f' => consumer(0x0C),
                    b'n' => consumer(b'\n'),
                    b'r' => consumer(b'\r'),
                    b't' => consumer(b'\t'),
                    b'u' => {
                        let c = self.read_unicode_escape_char()?;
                        let mut char_encode_buf = [0; 4];
                        let bytes_count = c.encode_utf8(&mut char_encode_buf).len();
                        for b in &char_encode_buf[..bytes_count] {
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
                self.column += 1;
                return Ok(true);
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
            // Read and validate UTF-8 encoded data
            _ => {
                self.read_utf8_bytes(byte, consumer)?;
            }
        }

        // Update column afterwards, so in case of error start position of escape sequence or multi-byte UTF-8 char is reported
        self.column += consumed_chars_count;
        Ok(false)
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

    fn read_string_bytes_to_string(&mut self) -> Result<String, StringReadingError> {
        let mut buf = Vec::new();
        self.read_all_string_bytes(&mut |byte| buf.push(byte))?;
        // Unwrap should be safe since reader made sure UTF-8 content is valid
        Ok(String::from_utf8(buf).unwrap())
    }

    /// Consumes the next member name
    ///
    /// `read_name` should read the name and if desired update the JSON path. The `Self`
    /// parameter of the function is `self`; this is necessary for callers to avoid directly
    /// accessing `self` which would not be permitted since `consume_name` is already called
    /// on `self`.
    fn consume_name<T, F: FnOnce(&mut Self) -> Result<T, ReaderError>>(
        &mut self,
        read_name: F,
    ) -> Result<T, ReaderError> {
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
        self.consume_peeked();

        // TODO: Is there a cleaner solution than having to pass `self` as argument to `read_name`?
        let result = read_name(self)?;

        let byte = self.skip_whitespace_no_eof(SyntaxErrorKind::MissingColon)?;
        return if byte == b':' {
            self.skip_peeked_byte();
            self.column += 1;
            Ok(result)
        } else {
            self.create_syntax_value_error(SyntaxErrorKind::MissingColon)
        };
    }

    fn skip_name_impl(&mut self, update_path: bool) -> Result<(), ReaderError> {
        self.consume_name(|self_| {
            if update_path {
                // Similar to `next_name` implementation, except that `name` can directly be moved to
                // json_path piece instead of having to be cloned
                let name = self_.read_string_bytes_to_string()?;

                match self_.json_path.last_mut().unwrap() {
                    JsonPathPiece::ObjectMember(path_name) => *path_name = name,
                    _ => unreachable!("Path should be object member"),
                }
            } else {
                self_.skip_all_string_bytes()?;
                // Don't update the path, but keep the initial member name
                // TODO: In the future when `update_path == false` don't update the path at all (neither push nor pop path pieces)?
                //       Would require passing `update_path` to all kinds of methods though, e.g. `next_bool`, `begin_array`, ...
                //       In that case would also have to indicate that path is incomplete, e.g. by appending " (incomplete)"?
            }
            Ok(())
        })
    }

    fn collect_next_number_bytes<C: FnMut(u8)>(
        &mut self,
        consumer: &mut C,
    ) -> Result<(), ReaderError> {
        self.start_expected_value_type(ValueType::Number)?;

        // unwrap() is safe because start_expected_value_type already peeked at first number byte
        let first_byte = self.peek_byte()?.unwrap();
        let mut consumed_bytes = 0;
        let number_result = consume_json_number(
            &mut || {
                // Should not fail since last peek_byte() succeeded
                self.skip_peeked_byte();
                self.peek_byte()
            },
            &mut |byte| {
                consumed_bytes += 1;
                consumer(byte);
            },
            first_byte,
        )?;
        let exponent_digits_count = match number_result {
            None => return self.create_syntax_value_error(SyntaxErrorKind::MalformedNumber),
            Some(exponent_digits_count) => exponent_digits_count,
        };

        // Note: This currently also affects skip_value (and its callers); maybe restricting number
        // values during skipping is not really necessary
        if self.reader_settings.restrict_number_values {
            // >= e100, <= e-100 or complete number longer than 100 chars
            if exponent_digits_count > 2 || consumed_bytes > 100 {
                return Err(ReaderError::UnsupportedNumberValue(
                    self.create_error_location(),
                ));
            }
        }

        self.column += consumed_bytes;
        // Make sure there are no misleading chars directly afterwards, e.g. "123f"
        if let Some(byte) = self.peek_byte()? {
            self.verify_value_separator(byte, SyntaxErrorKind::TrailingDataAfterNumber)?
        }

        self.on_value_end();
        Ok(())
    }
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
        self.json_path.push(JsonPathPiece::ArrayItem(0));
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
        // Push a placeholder which is replaced once the name of the first member is read
        // Important: When changing this placeholder in the future also have to update documentation mentioning to it
        self.json_path
            .push(JsonPathPiece::ObjectMember("<?>".to_owned()));
        self.is_empty = true;
        self.expects_member_name = true;
        Ok(())
    }

    fn next_name(&mut self) -> Result<String, ReaderError> {
        self.consume_name(|self_| {
            let name = self_.read_string_bytes_to_string()?;

            match self_.json_path.last_mut().unwrap() {
                JsonPathPiece::ObjectMember(path_name) => *path_name = name.clone(),
                _ => unreachable!("Path should be object member"),
            }
            Ok(name)
        })
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

    fn next_number<T: FromStr>(&mut self) -> Result<Result<T, T::Err>, ReaderError> {
        Ok(T::from_str(self.next_number_as_string()?.as_str()))
    }

    fn has_next(&mut self) -> Result<bool, ReaderError> {
        if self.expects_member_value() {
            panic!(
                    "Incorrect reader usage: Cannot check for next element when member value is expected"
                );
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
        // Update path when skipping name, otherwise errors when reading
        // corresponding member value will have wrong path
        self.skip_name_impl(true)
    }

    fn skip_value(&mut self) -> Result<(), ReaderError> {
        if self.expects_member_name {
            panic!("Incorrect reader usage: Cannot skip value when expecting member name");
        } else {
            let update_path = self.reader_settings.update_path_during_skip;
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
                        self.skip_name_impl(update_path)?;
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
                            self.collect_next_number_bytes(&mut |_| {})?;
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
        }

        Ok(())
    }

    fn next_string(&mut self) -> Result<String, ReaderError> {
        self.start_expected_value_type(ValueType::String)?;
        let result = Ok(self.read_string_bytes_to_string()?);
        self.on_value_end();
        result
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
        }))
    }

    fn next_number_as_string(&mut self) -> Result<String, ReaderError> {
        let mut buf = Vec::new();
        self.collect_next_number_bytes(&mut |byte| buf.push(byte))?;
        // Unwrap should be safe since number bytes are valid UTF-8 chars
        Ok(String::from_utf8(buf).unwrap())
    }

    #[cfg(feature = "serde")]
    fn deserialize_next<'de, D: serde::de::Deserialize<'de>>(
        &mut self,
    ) -> Result<D, crate::serde::DeserializerError> {
        // peek here to fail fast if reader is currently not expecting a value
        self.peek()?;
        let mut deserializer = crate::serde::JsonReaderDeserializer::new(self);
        D::deserialize(&mut deserializer)
        // TODO: Verify that value was properly deserialized (only single value; no incomplete array or object)
        // might not be necessary because Serde's Deserializer API enforces this by consuming `self`, and
        // JsonReaderDeserializer makes sure JSON arrays and objects are read completely
    }

    fn seek_to(&mut self, rel_json_path: &JsonPath) -> Result<(), ReaderError> {
        for path_piece in rel_json_path {
            match path_piece {
                JsonPathPiece::ArrayItem(index) => {
                    self.begin_array()?;
                    for i in 0..=*index {
                        if !self.has_next()? {
                            return Err(ReaderError::UnexpectedStructure {
                                kind: UnexpectedStructureKind::TooShortArray {
                                    expected_index: *index,
                                },
                                location: self.create_error_location(),
                            });
                        }

                        // Last iteration only makes sure has_next() succeeds; don't have to skip value
                        if i < *index {
                            self.skip_value()?;
                        }
                    }
                }
                JsonPathPiece::ObjectMember(name) => {
                    self.begin_object()?;

                    let mut found_member = false;
                    while self.has_next()? {
                        if self.next_name()?.eq(name) {
                            found_member = true;
                            break;
                        } else {
                            self.skip_value()?;
                        }
                    }

                    if !found_member {
                        return Err(ReaderError::UnexpectedStructure {
                            kind: UnexpectedStructureKind::MissingObjectMember {
                                member_name: name.clone(),
                            },
                            location: self.create_error_location(),
                        });
                    }
                }
            }
        }

        Ok(())
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
                        // Uses variant which updates the JSON path when skipping the name, otherwise the error
                        // location would point to name of an unrelated previously consumed member in the same object
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
                    json_writer.name(&name)?;
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

                        let mut buf = [0_u8; 4];
                        let mut buf_len;
                        loop {
                            buf_len = 0;
                            let reached_end = self
                                .read_string_bytes(&mut |byte| {
                                    buf[buf_len] = byte;
                                    buf_len += 1;
                                })
                                .map_err(ReaderError::from)?;

                            if reached_end {
                                break;
                            } else {
                                string_writer.write_all(&buf[..buf_len])?;
                            }
                        }
                        string_writer.finish_value()?;
                        self.on_value_end();
                    }
                    ValueType::Number => {
                        let number = self.next_number_as_string()?;
                        // Should not fail since next_number_as_string would have returned Err for invalid JSON number
                        if let Err(e) = json_writer.number_value_from_string(&number) {
                            match e {
                                JsonNumberError::InvalidNumber(e) => panic!("Unexpected: JSON writer rejected valid JSON number '{number}': {e}"),
                                JsonNumberError::IoError(e) => return Err(TransferError::WriterError(e)),
                            }
                        }
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
}

impl<'j, R: Read> Read for StringValueReader<'j, R> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
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
                    StringReadingError::IoError(e) => return Err(e),
                },
            }
        }
        Ok(pos)
    }
}

#[cfg(test)]
mod tests {
    use crate::writer::{FloatingPointNumber, IntegralNumber, JsonStreamWriter, StringValueWriter};

    use super::*;

    type TestResult = Result<(), Box<dyn std::error::Error>>;

    fn new_reader(json: &str) -> JsonStreamReader<&[u8]> {
        JsonStreamReader::new(json.as_bytes())
    }

    trait IterAssert: IntoIterator
    where
        Self::Item: Display,
    {
        fn assert_all<A: Fn(&Self::Item) -> TestResult>(self, assert: A)
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

    fn assert_parse_error_with_path<T>(
        // input is only used for display purposes; enhances error messages for loops testing multiple inputs
        input: Option<&str>,
        result: Result<T, ReaderError>,
        expected_kind: SyntaxErrorKind,
        expected_path: &str,
        expected_column: u32,
    ) {
        let input_display_str = input.map_or("".to_owned(), |s| " for '".to_owned() + s + "'");
        match result {
            Ok(_) => panic!("Test should have failed{}", input_display_str),
            Err(e) => match e {
                ReaderError::SyntaxError(e) => assert_eq!(
                    JsonSyntaxError {
                        kind: expected_kind,
                        location: JsonErrorLocation {
                            path: expected_path.to_owned(),
                            line: 0,
                            column: expected_column
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

    fn assert_parse_error<T>(
        input: Option<&str>,
        result: Result<T, ReaderError>,
        expected_kind: SyntaxErrorKind,
        expected_column: u32,
    ) {
        assert_parse_error_with_path(input, result, expected_kind, "$", expected_column);
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
            let json = "true".to_owned() + whitespace;
            let mut json_reader = new_reader(json.as_str());
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
        assert_eq!("a", json_reader.next_name()?);
        assert_eq!(true, json_reader.next_bool()?);
        json_reader.end_object()?;

        let mut json_reader = new_reader_with_comments("true// a");
        assert_eq!(true, json_reader.next_bool()?);
        json_reader.consume_trailing_whitespace()?;

        Ok(())
    }

    #[test]
    fn numbers_as_string() -> TestResult {
        let mut json_reader =
            new_reader("[0, -0, -1, -9, 123, 56.0030, -0.1, 1.01e+03, -4.50E-40]");
        let mut actual = Vec::new();

        json_reader.begin_array()?;
        while json_reader.has_next()? {
            actual.push(json_reader.next_number_as_string()?);
        }
        json_reader.end_array()?;
        json_reader.consume_trailing_whitespace()?;

        let expected = vec![
            "0",
            "-0",
            "-1",
            "-9",
            "123",
            "56.0030",
            "-0.1",
            "1.01e+03",
            "-4.50E-40",
        ];
        assert_eq!(expected, actual);

        Ok(())
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
        let mut json_reader = new_reader("1e99");
        assert_eq!("1e99", json_reader.next_number_as_string()?);

        let mut json_reader = new_reader("1e+99");
        assert_eq!("1e+99", json_reader.next_number_as_string()?);

        let mut json_reader = new_reader("1e-99");
        assert_eq!("1e-99", json_reader.next_number_as_string()?);

        let number = "1".repeat(100);
        let mut json_reader = new_reader(&number);
        assert_eq!(number, json_reader.next_number_as_string()?);

        fn assert_unsupported_number(json: &str) {
            let mut json_reader = new_reader(json);
            match json_reader.next_number_as_string() {
                Err(ReaderError::UnsupportedNumberValue(location)) => {
                    assert_eq!(
                        JsonErrorLocation {
                            line: 0,
                            column: 0,
                            path: "$".to_owned(),
                        },
                        location
                    );
                }
                r => panic!("Unexpected result: {r:?}"),
            }

            let mut json_reader = new_reader(json);
            match json_reader.next_number::<f64>() {
                Err(ReaderError::UnsupportedNumberValue(location)) => {
                    assert_eq!(
                        JsonErrorLocation {
                            line: 0,
                            column: 0,
                            path: "$".to_owned(),
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
        assert_unsupported_number(&"1".repeat(101));

        // TODO: These should actually be supported, but implementing this might be difficult,
        // especially for skipping of numbers; not sure if that is worth it
        assert_unsupported_number("1e0000");
        assert_unsupported_number("1e005");

        let json = format!("[1e100, 1e+100, 1e-100, {}]", "1".repeat(101));
        let mut json_reader = JsonStreamReader::new_custom(
            json.as_bytes(),
            ReaderSettings {
                restrict_number_values: false,
                ..Default::default()
            },
        );
        json_reader.begin_array()?;
        assert_eq!("1e100", json_reader.next_number_as_string()?);
        assert_eq!("1e+100", json_reader.next_number_as_string()?);
        assert_eq!("1e-100", json_reader.next_number_as_string()?);
        assert_eq!("1".repeat(101), json_reader.next_number_as_string()?);
        json_reader.end_array()?;

        Ok(())
    }

    #[test]
    fn strings() -> TestResult {
        let json = r#"["", "a b", "a\"b", "a\\\\\"b", "a\\", "\"\\\/\b\f\n\r\t\u0000\u0080\u0800\u12345\uD852\uDF62 \u1234\u5678\u90AB\uCDEF\uabcd\uefEF","#.to_owned() + "\"\u{007F}\u{0080}\u{07FF}\u{0800}\u{FFFF}\u{10000}\u{10FFFF}\",\"\u{2028}\u{2029}\"]";
        let mut json_reader = new_reader(json.as_str());
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
        fn assert_invalid(json: &str, expected_kind: SyntaxErrorKind, expected_column: u32) {
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
                Ok(_) => panic!("Test should have failed for: {:?}", string_content),
                Err(e) => match e {
                    ReaderError::IoError(e) => {
                        assert_eq!(ErrorKind::InvalidData, e.kind());
                        assert_eq!("invalid UTF-8 data", e.to_string());
                    }
                    other => panic!("Unexpected error: {other}"),
                },
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
                    "JSON syntax error UnknownEscapeSequence at line 0, column 1 at path $",
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
                        location: JsonErrorLocation {
                            path: "$".to_owned(),
                            line: 0,
                            column: 1
                        }
                    },
                    cause
                );
            }
        }
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
            "$[0]",
            1,
        );

        let mut json_reader = new_reader("[1,]");
        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.peek(),
            SyntaxErrorKind::TrailingCommaNotEnabled,
            "$[1]",
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
            "$[0]",
            1,
        );

        let mut json_reader = new_reader_with_trailing_comma("[1,,]");
        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.peek(),
            SyntaxErrorKind::UnexpectedComma,
            "$[1]",
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
            "$",
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
            "$[1]",
            3,
        );

        let mut json_reader = new_reader("[1: 2]");
        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::UnexpectedColon,
            "$[1]",
            2,
        );

        let mut json_reader = new_reader(r#"["a": 1]"#);
        json_reader.begin_array()?;
        assert_eq!("a", json_reader.next_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::UnexpectedColon,
            "$[1]",
            4,
        );

        let mut json_reader = new_reader("[1}");
        json_reader.begin_array()?;
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::UnexpectedClosingBracket,
            "$[1]",
            2,
        );
        assert_parse_error_with_path(
            None,
            json_reader.end_array(),
            SyntaxErrorKind::UnexpectedClosingBracket,
            "$[1]",
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
            "$.<?>",
            1,
        );

        let mut json_reader = new_reader("{\"a\":1,}");
        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::TrailingCommaNotEnabled,
            "$.a",
            6,
        );

        let mut json_reader = new_reader_with_trailing_comma("{\"a\":1,}");
        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name()?);
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
            "$.<?>",
            1,
        );

        let mut json_reader = new_reader_with_trailing_comma("{\"a\":1,,}");
        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            "$.a",
            7,
        );

        Ok(())
    }

    #[test]
    fn object_member_names() -> TestResult {
        let mut json_reader = new_reader(r#"{"": 1, "a": 2, "": 3, "a": 4}"#);
        json_reader.begin_object()?;

        assert_eq!("", json_reader.next_name()?);
        assert_eq!("1", json_reader.next_number_as_string()?);

        assert_eq!("a", json_reader.next_name()?);
        assert_eq!("2", json_reader.next_number_as_string()?);

        assert_eq!("", json_reader.next_name()?);
        assert_eq!("3", json_reader.next_number_as_string()?);

        assert_eq!("a", json_reader.next_name()?);
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
            "$.<?>",
            1,
        );
        assert_parse_error_with_path(
            None,
            json_reader.next_name(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            "$.<?>",
            1,
        );

        let mut json_reader = new_reader("{test: 1}");
        json_reader.begin_object()?;
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            "$.<?>",
            1,
        );
        assert_parse_error_with_path(
            None,
            json_reader.next_name(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            "$.<?>",
            1,
        );

        let mut json_reader = new_reader("{: 1}");
        json_reader.begin_object()?;
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            "$.<?>",
            1,
        );
        assert_parse_error_with_path(
            None,
            json_reader.next_name(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            "$.<?>",
            1,
        );

        let mut json_reader = new_reader(r#"{"a":: 1}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_eq!("a", json_reader.next_name()?);
        assert_parse_error_with_path(
            None,
            json_reader.next_number_as_string(),
            SyntaxErrorKind::UnexpectedColon,
            "$.a",
            5,
        );

        let mut json_reader = new_reader(r#"{"a"}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_parse_error_with_path(
            None,
            json_reader.next_name(),
            SyntaxErrorKind::MissingColon,
            "$.a",
            4,
        );

        let mut json_reader = new_reader(r#"{"a":}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_eq!("a", json_reader.next_name()?);
        assert_parse_error_with_path(
            None,
            json_reader.peek(),
            SyntaxErrorKind::UnexpectedClosingBracket,
            "$.a",
            5,
        );

        let mut json_reader = new_reader(r#"{"a" 1}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_parse_error_with_path(
            None,
            json_reader.next_name(),
            SyntaxErrorKind::MissingColon,
            "$.a",
            5,
        );

        let mut json_reader = new_reader(r#"{"a", "b": 2}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_parse_error_with_path(
            None,
            json_reader.next_name(),
            SyntaxErrorKind::MissingColon,
            "$.a",
            4,
        );

        let mut json_reader = new_reader(r#"{"a": 1 "b": 2}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_eq!("a", json_reader.next_name()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::MissingComma,
            "$.a",
            8,
        );
        assert_parse_error_with_path(
            None,
            json_reader.next_name(),
            SyntaxErrorKind::MissingComma,
            "$.a",
            8,
        );

        let mut json_reader = new_reader(r#"{"a": 1,, "b": 2}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_eq!("a", json_reader.next_name()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            "$.a",
            8,
        );
        /* TODO: Reader currently already advances after duplicate comma, so this won't fail
         *   However it is already documented that continuing after syntax error causes unspecified behavior
        assert_parse_error_with_path(
            None,
            json_reader.next_name(),
            SyntaxErrorKind::MalformedJson,
            "$.a",
            8,
        );
         */

        let mut json_reader = new_reader(r#"{"a": 1: "b": 2}"#);
        json_reader.begin_object()?;
        assert!(json_reader.has_next()?);
        assert_eq!("a", json_reader.next_name()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd, // Maybe a bit misleading because it also expects comma?
            "$.a",
            7,
        );
        assert_parse_error_with_path(
            None,
            json_reader.next_name(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            "$.a",
            7,
        );

        let mut json_reader = new_reader("{]");
        json_reader.begin_object()?;
        assert_parse_error_with_path(
            None,
            json_reader.has_next(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            "$.<?>",
            1,
        );
        assert_parse_error_with_path(
            None,
            json_reader.next_name(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            "$.<?>",
            1,
        );
        assert_parse_error_with_path(
            None,
            json_reader.end_object(),
            SyntaxErrorKind::ExpectingMemberNameOrObjectEnd,
            "$.<?>",
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
        assert_eq!("a", json_reader.next_name().unwrap());

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
            "$[14]",
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
        let mut json_reader = new_reader(json.as_str());

        json_reader.skip_value()?;
        json_reader.consume_trailing_whitespace()?;

        // Also test with malformed JSON to verify that deeply nested value is actually reached
        let json = "[".repeat(nesting_depth) + "@" + "]".repeat(nesting_depth).as_str();
        let mut json_reader = new_reader(json.as_str());
        assert_parse_error_with_path(
            None,
            json_reader.skip_value(),
            SyntaxErrorKind::MalformedJson,
            ("$".to_owned() + "[0]".repeat(nesting_depth).as_str()).as_str(),
            nesting_depth as u32,
        );

        Ok(())
    }

    #[test]
    fn skip_no_path_update() -> TestResult {
        fn new_reader_no_path_update(json: &str) -> JsonStreamReader<&[u8]> {
            JsonStreamReader::new_custom(
                json.as_bytes(),
                ReaderSettings {
                    update_path_during_skip: false,
                    ..Default::default()
                },
            )
        }

        let mut json_reader =
            new_reader_no_path_update(r#"[{"a": 1, "b": [{"c": {}, "d": []}, true]}, 2]"#);
        json_reader.begin_array()?;
        json_reader.skip_value()?;
        assert_unexpected_structure(
            json_reader.end_array(),
            UnexpectedStructureKind::MoreElementsThanExpected,
            "$[1]",
            44,
        );
        assert_eq!("2", json_reader.next_number_as_string()?);
        json_reader.end_array()?;

        let mut json_reader = new_reader_no_path_update(r#"{"a": 1, "b": [{"c": @}]}"#);
        assert_parse_error_with_path(
            None,
            json_reader.skip_value(),
            SyntaxErrorKind::MalformedJson,
            "$.<?>[0].<?>",
            21,
        );

        let mut json_reader = new_reader_no_path_update(r#"{"a": {"b": 1}}"#);
        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name()?);
        // Skipping object should not affect path of current object
        json_reader.skip_value()?;
        assert_unexpected_structure(
            json_reader.next_name(),
            UnexpectedStructureKind::FewerElementsThanExpected,
            "$.a",
            14,
        );

        let mut json_reader = new_reader_no_path_update(r#"{"a": @}"#);
        json_reader.begin_object()?;
        // When only skipping name it should still be stored in path regardless of reader settings
        json_reader.skip_name()?;
        assert_parse_error_with_path(
            None,
            json_reader.peek(),
            SyntaxErrorKind::MalformedJson,
            "$.a",
            6,
        );

        Ok(())
    }

    #[test]
    fn skip_object() -> TestResult {
        let mut json_reader = new_reader(r#"{"a": {"a1": [1, []]}, "b": 2, "c": 3}"#);
        json_reader.begin_object()?;

        assert_eq!("a", json_reader.next_name()?);
        json_reader.skip_value()?;

        assert_eq!("b", json_reader.next_name()?);
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
        let mut json_reader = new_reader(json.as_str());

        json_reader.skip_value()?;
        json_reader.consume_trailing_whitespace()?;

        // Also test with malformed JSON to verify that deeply nested value is actually reached
        let json = json_start.repeat(nesting_depth) + "@" + "}".repeat(nesting_depth).as_str();
        let mut json_reader = new_reader(json.as_str());
        assert_parse_error_with_path(
            None,
            json_reader.skip_value(),
            SyntaxErrorKind::MalformedJson,
            ("$".to_owned() + ".a".repeat(nesting_depth).as_str()).as_str(),
            (json_start.len() * nesting_depth) as u32,
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
            "$[0]",
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
        assert_eq!("a", json_reader.next_name()?);
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
            "$[0]",
            1,
        );

        Ok(())
    }

    #[test]
    fn skip_to_top_level_no_path_update() -> TestResult {
        fn new_reader_no_path_update(json: &str) -> JsonStreamReader<&[u8]> {
            JsonStreamReader::new_custom(
                json.as_bytes(),
                ReaderSettings {
                    update_path_during_skip: false,
                    ..Default::default()
                },
            )
        }

        let mut json_reader = new_reader_no_path_update(r#"{"a": 1, "b": @}"#);
        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name()?);
        assert_parse_error_with_path(
            None,
            json_reader.skip_to_top_level(),
            SyntaxErrorKind::MalformedJson,
            // Path in already started objects should have been updated
            "$.b",
            14,
        );

        let mut json_reader = new_reader_no_path_update(r#"{"a": {"b": @}}"#);
        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name()?);
        assert_parse_error_with_path(
            None,
            json_reader.skip_to_top_level(),
            SyntaxErrorKind::MalformedJson,
            "$.a.<?>",
            12,
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
        let mut json_reader = new_reader(json.as_str());
        json_reader.begin_array()?;

        let mut writer = Vec::<u8>::new();
        let mut json_writer = JsonStreamWriter::new(&mut writer);
        json_writer.begin_array()?;

        while json_reader.has_next()? {
            json_reader.transfer_to(&mut json_writer)?;
        }
        // Also check how missing value is handled
        assert_unexpected_structure(
            json_reader
                .transfer_to(&mut json_writer)
                .map_err(as_transfer_read_error),
            UnexpectedStructureKind::FewerElementsThanExpected,
            "$[8]",
            99,
        );

        json_reader.end_array()?;
        json_reader.consume_trailing_whitespace()?;

        json_writer.end_array()?;
        json_writer.finish_document()?;
        assert_eq!(
            r#"[true,null,123,123.0e+0,"a\"b\\cd",[1],{"a":1,"a\"b\\cd":2,"c":[{"d":[3]}]},"#
                .to_owned()
                + "\"\u{10FFFF}\"]",
            std::str::from_utf8(&writer)?
        );

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
        assert_eq!("[1,2]", std::str::from_utf8(&writer)?);

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

            fn number_value<N: IntegralNumber>(&mut self, _: N) -> Result<(), IoError> {
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
                        panic!("Unexpected error for input '{json}': {e}")
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
        expected_path: &str,
        expected_column: u32,
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
                        JsonErrorLocation {
                            path: expected_path.to_string(),
                            line: 0,
                            column: expected_column
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
        expected_path: &str,
        expected_column: u32,
    ) {
        match result {
            Ok(_) => panic!("Test should have failed"),
            Err(e) => match e {
                ReaderError::UnexpectedStructure { kind, location } => {
                    assert_eq!(expected_kind, kind);
                    assert_eq!(
                        JsonErrorLocation {
                            path: expected_path.to_string(),
                            line: 0,
                            column: expected_column
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

    #[test]
    fn seek_to_unexpected_structure() -> TestResult {
        let mut json_reader = new_reader("[]");
        assert_unexpected_structure(
            json_reader.seek_to(&[JsonPathPiece::ArrayItem(0)]),
            UnexpectedStructureKind::TooShortArray { expected_index: 0 },
            "$[0]",
            1,
        );

        let mut json_reader = new_reader("[1]");
        assert_unexpected_structure(
            json_reader.seek_to(&[JsonPathPiece::ArrayItem(1)]),
            UnexpectedStructureKind::TooShortArray { expected_index: 1 },
            "$[1]",
            2,
        );

        let mut json_reader = new_reader(r#"{"a": 1}"#);
        assert_unexpected_structure(
            json_reader.seek_to(&[JsonPathPiece::ObjectMember("b".to_owned())]),
            UnexpectedStructureKind::MissingObjectMember {
                member_name: "b".to_owned(),
            },
            "$.a",
            7,
        );

        let mut json_reader = new_reader("1");
        assert_unexpected_value_type(
            json_reader.seek_to(&[JsonPathPiece::ArrayItem(0)]),
            ValueType::Array,
            ValueType::Number,
            "$",
            0,
        );

        let mut json_reader = new_reader("1");
        assert_unexpected_value_type(
            json_reader.seek_to(&[JsonPathPiece::ObjectMember("a".to_owned())]),
            ValueType::Object,
            ValueType::Number,
            "$",
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
            "$[0]",
            1,
        );
        assert_unexpected_structure(
            json_reader.next_bool(),
            UnexpectedStructureKind::FewerElementsThanExpected,
            "$[0]",
            1,
        );

        let mut json_reader = new_reader("[1]");
        json_reader.begin_array()?;
        assert_unexpected_structure(
            json_reader.end_array(),
            UnexpectedStructureKind::MoreElementsThanExpected,
            "$[0]",
            1,
        );

        let mut json_reader = new_reader("{}");
        json_reader.begin_object()?;
        assert_unexpected_structure(
            json_reader.next_name(),
            UnexpectedStructureKind::FewerElementsThanExpected,
            "$.<?>",
            1,
        );

        let mut json_reader = new_reader(r#"{"a": 1}"#);
        json_reader.begin_object()?;
        assert_unexpected_structure(
            json_reader.end_object(),
            UnexpectedStructureKind::MoreElementsThanExpected,
            "$.<?>",
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
            "$",
            0,
        );
        assert_unexpected_value_type(
            json_reader.next_null(),
            ValueType::Null,
            ValueType::Number,
            "$",
            0,
        );
        assert_unexpected_value_type(
            json_reader.next_string(),
            ValueType::String,
            ValueType::Number,
            "$",
            0,
        );
        assert_unexpected_value_type(
            json_reader.begin_array(),
            ValueType::Array,
            ValueType::Number,
            "$",
            0,
        );
        assert_unexpected_value_type(
            json_reader.begin_object(),
            ValueType::Object,
            ValueType::Number,
            "$",
            0,
        );

        let mut json_reader = new_reader("true");
        assert_unexpected_value_type(
            json_reader.next_number_as_string(),
            ValueType::Number,
            ValueType::Boolean,
            "$",
            0,
        );

        let mut json_reader = new_reader("false");
        assert_unexpected_value_type(
            json_reader.next_null(),
            ValueType::Null,
            ValueType::Boolean,
            "$",
            0,
        );

        let mut json_reader = new_reader("null");
        assert_unexpected_value_type(
            json_reader.next_bool(),
            ValueType::Boolean,
            ValueType::Null,
            "$",
            0,
        );

        let mut json_reader = new_reader("\"ab\"");
        assert_unexpected_value_type(
            json_reader.next_bool(),
            ValueType::Boolean,
            ValueType::String,
            "$",
            0,
        );

        let mut json_reader = new_reader("[]");
        assert_unexpected_value_type(
            json_reader.next_bool(),
            ValueType::Boolean,
            ValueType::Array,
            "$",
            0,
        );

        let mut json_reader = new_reader("{}");
        assert_unexpected_value_type(
            json_reader.next_bool(),
            ValueType::Boolean,
            ValueType::Object,
            "$",
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
            "$",
            7,
        );
        assert_unexpected_structure(
            json_reader.next_bool(),
            UnexpectedStructureKind::FewerElementsThanExpected,
            "$",
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
        assert_eq!("a", json_reader.next_name().unwrap());

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
        assert_eq!("a", json_reader.next_name()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_eq!("b", json_reader.next_name()?);
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
        match json_reader.peek() {
            Ok(_) => panic!("Test should have failed"),
            Err(e) => match e {
                ReaderError::IoError(e) => {
                    assert_eq!(ErrorKind::InvalidData, e.kind());
                    assert_eq!("invalid UTF-8 data", e.to_string());
                }
                other => panic!("Unexpected error: {other}"),
            },
        }

        Ok(())
    }

    #[test]
    fn location_whitespace() {
        fn assert_location(json: &str, expected_line: u32, expected_column: u32) {
            let mut json_reader = new_reader_with_comments(json);
            match json_reader.peek() {
                Ok(_) => panic!("Test should have failed"),
                Err(e) => match e {
                    ReaderError::SyntaxError(e) => assert_eq!(
                        JsonSyntaxError {
                            kind: SyntaxErrorKind::IncompleteDocument,
                            location: JsonErrorLocation {
                                path: "$".to_owned(),
                                line: expected_line,
                                column: expected_column
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

        assert_location("", 0, 0);
        assert_location(" ", 0, 1);
        assert_location("\t", 0, 1);
        assert_location("\n", 1, 0);
        assert_location("\r", 1, 0);
        assert_location("\r\n", 1, 0);
        assert_location("\r \n", 2, 0);
        assert_location("\n\r", 2, 0);
        assert_location("\r\n\n", 2, 0);
        assert_location("\r\r", 2, 0);
        assert_location("\r\r\n", 2, 0);
        assert_location("\n  \r \t \r\n    \t\t ", 3, 7);

        assert_location("//\n", 1, 0);
        assert_location("//\n  ", 1, 2);
        assert_location("//\n  //\r  // a", 2, 6);

        assert_location("/* */", 0, 5);
        assert_location("/* */\n ", 1, 1);
        assert_location("/* \n \r */  ", 2, 5);
        // Multi-byte UTF-8 encoded char should be considered only 1 column
        assert_location("/*\u{10FFFF}*/", 0, 5);
    }

    #[test]
    fn location_value() {
        fn assert_location(json: &str, expected_column: u32) {
            let mut json_reader = new_reader(json);
            json_reader.begin_array().unwrap();
            json_reader.skip_value().unwrap();
            assert_parse_error_with_path(
                Some(json),
                json_reader.peek(),
                SyntaxErrorKind::IncompleteDocument,
                "$[1]",
                expected_column,
            );
        }

        assert_location("[true,", 6);
        assert_location("[false,", 7);
        assert_location("[null,", 6);
        assert_location("[123e1,", 7);
        assert_location(r#"["","#, 4);
        assert_location(r#"["\"\\\/\b\f\n\r\t\u1234","#, 26);
        // Escaped line breaks should not be considered line breaks
        assert_location(r#"["\n \r","#, 9);
        assert_location(r#"["\u000A \u000D","#, 17);
        // Multi-byte UTF-8 encoded character should be considered single character
        assert_location("[\"\u{10FFFF}\",", 5);
        // Line separator and line paragraph should not be considered line breaks
        assert_location("[\"\u{2028}\u{2029}\",", 6);
        assert_location("[[],", 4);
        assert_location("[[1, 2],", 8);
        assert_location("[{},", 4);
        assert_location(r#"[{"a": 1},"#, 10);
    }

    #[test]
    fn location_malformed_name() -> TestResult {
        let mut json_reader = new_reader("{\"a\": 1, \"b\\X\": 2}");
        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name()?);
        assert_eq!("1", json_reader.next_number_as_string()?);
        assert_parse_error_with_path(
            None,
            json_reader.next_name(),
            SyntaxErrorKind::UnknownEscapeSequence,
            "$.a",
            11,
        );

        Ok(())
    }

    #[test]
    fn location_skip() -> TestResult {
        let mut json_reader =
            new_reader(r#"[true, false, null, 12, "test", [], [34], {}, {"a": 1}]"#);
        json_reader.begin_array()?;

        for (i, column_position) in [1, 7, 14, 20, 24, 32, 36, 42, 46].iter().enumerate() {
            let expected_path = format!("$[{i}]");
            assert_unexpected_structure(
                json_reader.end_array(),
                UnexpectedStructureKind::MoreElementsThanExpected,
                &expected_path,
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
            "$.<?>",
            1,
        );

        json_reader.skip_name()?;
        assert_unexpected_value_type(
            json_reader.next_bool(),
            ValueType::Boolean,
            ValueType::Number,
            "$.a",
            6,
        );

        json_reader.skip_value()?;

        assert_unexpected_structure(
            json_reader.end_object(),
            UnexpectedStructureKind::MoreElementsThanExpected,
            "$.a",
            9,
        );
        json_reader.skip_name()?;
        assert_unexpected_value_type(
            json_reader.next_bool(),
            ValueType::Boolean,
            ValueType::Number,
            "$.b",
            14,
        );

        json_reader.skip_value()?;

        assert_unexpected_structure(
            json_reader.next_name(),
            UnexpectedStructureKind::FewerElementsThanExpected,
            "$.b",
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
        let json = "[".to_owned() + "true,".repeat(count - 1).as_str() + "true]";
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
        let json = "[".to_owned() + "true,".repeat(count - 1).as_str() + "true]";
        let mut json_reader = new_reader(json.as_str());

        json_reader.begin_array()?;
        for _ in 0..count {
            assert_eq!(true, json_reader.next_bool()?);
        }
        json_reader.end_array()?;
        assert_eq!(json.len() as u32, json_reader.column);
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

    impl<'a> Read for DebuggableReader<'a> {
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

    impl<'a> Debug for DebuggableReader<'a> {
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
            "JsonStreamReader { reader: debuggable-reader, buf_count: 0, buf_str: \"\", peeked: None, is_empty: true, expects_member_name: false, stack: [], is_string_value_reader_active: false, line: 0, column: 0, json_path: [], reader_settings: ReaderSettings { allow_comments: false, allow_trailing_comma: false, allow_multiple_top_level: false, update_path_during_skip: true, restrict_number_values: true } }",
            format!("{json_reader:?}")
        );

        assert_eq!(ValueType::Number, json_reader.peek()?);
        assert_eq!(
            "JsonStreamReader { reader: debuggable-reader, buf_count: 3, buf_str: \"123\", peeked: Some(NumberStart), is_empty: true, expects_member_name: false, stack: [], is_string_value_reader_active: false, line: 0, column: 0, json_path: [], reader_settings: ReaderSettings { allow_comments: false, allow_trailing_comma: false, allow_multiple_top_level: false, update_path_during_skip: true, restrict_number_values: true } }",
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
            "JsonStreamReader { reader: debuggable-reader, buf_count: 600, buf_str: \"123456123456123456123456123456123456123456123...\", peeked: Some(NumberStart), is_empty: true, expects_member_name: false, stack: [], is_string_value_reader_active: false, line: 0, column: 0, json_path: [], reader_settings: ReaderSettings { allow_comments: false, allow_trailing_comma: false, allow_multiple_top_level: false, update_path_during_skip: true, restrict_number_values: false } }",
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
            "JsonStreamReader { reader: debuggable-reader, buf_count: 15, buf_str: \"this is a test...\", ...buf...: [195], peeked: Some(StringStart), is_empty: true, expects_member_name: false, stack: [], is_string_value_reader_active: false, line: 0, column: 0, json_path: [], reader_settings: ReaderSettings { allow_comments: false, allow_trailing_comma: false, allow_multiple_top_level: false, update_path_during_skip: true, restrict_number_values: true } }",
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
            "JsonStreamReader { reader: debuggable-reader, buf_count: 2, buf_str: \"a...\", ...buf...: [255], peeked: Some(StringStart), is_empty: true, expects_member_name: false, stack: [], is_string_value_reader_active: false, line: 0, column: 0, json_path: [], reader_settings: ReaderSettings { allow_comments: false, allow_trailing_comma: false, allow_multiple_top_level: false, update_path_during_skip: true, restrict_number_values: true } }",
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
            "JsonStreamReader { reader: debuggable-reader, buf_count: 121, buf_str: \"abcdefabcdefabcdefabcdefabcdefabcdefabcdefabc...\", peeked: Some(StringStart), is_empty: true, expects_member_name: false, stack: [], is_string_value_reader_active: false, line: 0, column: 0, json_path: [], reader_settings: ReaderSettings { allow_comments: false, allow_trailing_comma: false, allow_multiple_top_level: false, update_path_during_skip: true, restrict_number_values: true } }",
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
        assert_eq!(number_json.len() as u32, json_reader.column);
        json_reader.consume_trailing_whitespace()?;
        Ok(())
    }

    #[test]
    fn large_string() -> TestResult {
        let count = READER_BUF_SIZE;
        let string_json = "abc\u{10FFFF}d\\u1234e\\n".repeat(count);
        let expected_string_value = "abc\u{10FFFF}d\u{1234}e\n".repeat(count);
        let json = "\"".to_owned() + string_json.as_str() + "\"";
        let mut json_reader = new_reader(json.as_str());

        assert_eq!(expected_string_value, json_reader.next_string()?);
        // `- (3 * count)` to account for \u{10FFFF} taking up 4 bytes but representing a single char
        assert_eq!((json.len() - (3 * count)) as u32, json_reader.column);
        json_reader.consume_trailing_whitespace()?;
        Ok(())
    }

    #[cfg(feature = "serde")]
    mod serde {
        use std::{collections::HashMap, vec};

        use ::serde::Deserialize;

        use crate::serde::DeserializerError;

        use super::*;

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
                        JsonErrorLocation {
                            path: "$".to_owned(),
                            line: 0,
                            column: 0
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
