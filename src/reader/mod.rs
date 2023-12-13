//! Module for reading JSON data
//!
//! [`JsonReader`] is the general trait for JSON readers, [`JsonStreamReader`] is an implementation
//! of it which reads a JSON document from a [`Read`] in a streaming way.

/// Module for JSON path
///
/// A JSON path consists of zero or more [`JsonPathPiece`] elements which either represent the index of a
/// JSON array item or the name of a JSON object member. These elements combined form the _path_ to a value
/// in a JSON document.
///
/// The macro [`json_path!`](json_path::json_path) and the function [`parse_json_path`](json_path::parse_json_path)
/// can be used to create a JSON path in a concise way.
///
/// JSON path was originally specified in [this article](https://goessner.net/articles/JsonPath/). However,
/// this module only supports a small subset needed for JSON reader functionality, most notably for reporting
/// the location of errors and for [`JsonReader::seek_to`].
///
/// Consider for example the following code:
/// ```
/// # use struson::reader::json_path::*;
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
#[allow(deprecated)] // TODO: Only for JsonPathParseError, remove this allow(deprecated) attribute once JsonPathParseError was removed
pub mod json_path {
    use std::str::FromStr;
    use thiserror::Error;

    /// A piece of a JSON path
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

    /// A JSON path
    ///
    /// A JSON path as represented by this module are zero or more [`JsonPathPiece`] elements.
    /// The macro [`json_path!`] and the function [`parse_json_path`] can be used to create
    /// a JSON path in a concise way.
    /* TODO: Check if it is somehow possible to implement Display for this (and reuse code from format_abs_json_path then) */
    pub type JsonPath = [JsonPathPiece];

    pub(crate) fn format_abs_json_path(json_path: &JsonPath) -> String {
        "$".to_string()
            + json_path
                .iter()
                .map(|p| match p {
                    JsonPathPiece::ArrayItem(index) => format!("[{index}]"),
                    JsonPathPiece::ObjectMember(name) => format!(".{name}"),
                })
                .collect::<String>()
                .as_str()
    }

    /// Error which occurred while [parsing a JSON path](parse_json_path)
    #[deprecated = "Only used by parse_json_path, which is deprecated"]
    #[derive(Error, Clone, Debug)]
    #[error("parse error at index {index}: {message}")]
    pub struct JsonPathParseError {
        /// Index (starting at 0) where the error occurred within the string
        pub index: usize,
        /// Message describing why the error occurred
        pub message: String,
    }

    /// Parses a JSON path in dot-notation, for example `outer[4].inner`
    ///
    /// This is a convenience function which allows obtaining a vector of [`JsonPathPiece`] from a string form.
    /// The path string must not start with `$` (respectively `$.`) and member names are limited to contain only
    /// `a`-`z`, `A`-`Z`, `0`-`9`, `-` and `_`. The path string must not be empty. For malformed path strings
    /// an error is returned.
    ///
    /// # Examples
    /// ```
    /// # #![allow(deprecated)]
    /// # use struson::reader::json_path::*;
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
    #[deprecated = "Use json_path! instead"]
    #[allow(deprecated)] // Allow usage of deprecated JsonPathParseError
    pub fn parse_json_path(path: &str) -> Result<Vec<JsonPathPiece>, JsonPathParseError> {
        if path.is_empty() {
            return Err(JsonPathParseError {
                index: 0,
                message: "empty path".to_owned(),
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
                message: "leading '.' is not allowed".to_owned(),
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
                            message: "missing ']' for array index".to_owned(),
                        })
                    }
                    Some(i) => i,
                };
                if end_index == index {
                    return Err(JsonPathParseError {
                        index,
                        message: "missing index value".to_owned(),
                    });
                }
                if path_bytes[index] == b'0' && end_index != index + 1 {
                    return Err(JsonPathParseError {
                        index,
                        message: "leading 0 is not allowed".to_owned(),
                    });
                }

                #[allow(clippy::needless_range_loop)] // Suggested replacement is too verbose
                for i in index..end_index {
                    if !path_bytes[i].is_ascii_digit() {
                        return Err(JsonPathParseError {
                            index: i,
                            message: "invalid index digit".to_owned(),
                        });
                    }
                }
                let path_index =
                    u32::from_str(&path[index..end_index]).map_err(|e| JsonPathParseError {
                        index,
                        message: format!("invalid index value: {e}"),
                    })?;
                parsed_path.push(JsonPathPiece::ArrayItem(path_index));
                index = end_index + 1;
            } else {
                let end_index = find_any(path_bytes, b'.', b'[', index).unwrap_or(path_bytes.len());
                if end_index == index {
                    return Err(JsonPathParseError {
                        index,
                        message: "missing member name".to_owned(),
                    });
                }

                #[allow(clippy::needless_range_loop)] // Suggested replacement is too verbose
                for i in index..end_index {
                    let b = path_bytes[i];
                    if !(b.is_ascii_alphanumeric() || b == b'-' || b == b'_') {
                        return Err(JsonPathParseError {
                            index: i,
                            message: "unsupported char in member name".to_owned(),
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
                        message: "expecting either '.' or '['".to_owned(),
                    })
                }
            }
        }

        Ok(parsed_path)
    }

    /// Creates a JSON path from path pieces
    ///
    /// The arguments to this macro represent the path pieces:
    /// - numbers of type `u32` are converted to [`JsonPathPiece::ArrayItem`]
    /// - strings are converted to [`JsonPathPiece::ObjectMember`]
    ///
    /// At least one path piece argument must be provided.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::json_path::*;
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

    // Re-export the macro to be available under the `struson::reader::json_path` module path
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
        #[allow(deprecated)]
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

            assert_parse_error("", 0, "empty path");
            assert_parse_error(".a", 0, "leading '.' is not allowed");
            assert_parse_error("[", 1, "missing ']' for array index");
            assert_parse_error("[1", 1, "missing ']' for array index");
            assert_parse_error("[1.a]", 2, "invalid index digit");
            assert_parse_error("[1a2]", 2, "invalid index digit");
            assert_parse_error("[01]", 1, "leading 0 is not allowed");
            assert_parse_error("[00]", 1, "leading 0 is not allowed");
            assert_parse_error("[-1]", 1, "invalid index digit");
            assert_parse_error(
                "[99999999999999999999999999999999999999999999]",
                1,
                // TODO: Should this test really check for specific Rust library message?
                "invalid index value: number too large to fit in target type",
            );
            assert_parse_error("[1[0]]", 2, "invalid index digit");
            assert_parse_error("[a]", 1, "invalid index digit");
            assert_parse_error("[1]1]", 3, "expecting either '.' or '['");
            assert_parse_error("[1]a", 3, "expecting either '.' or '['");
            assert_parse_error("a.", 2, "missing member name");
            assert_parse_error("a..b", 2, "missing member name");
            assert_parse_error("a.[1]", 2, "missing member name");
            assert_parse_error("%a", 0, "unsupported char in member name");
            assert_parse_error("a%", 1, "unsupported char in member name");

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

use std::{
    fmt::{Debug, Display, Formatter},
    io::Read,
    str::FromStr,
};

use thiserror::Error;

use self::json_path::{format_abs_json_path, JsonPath, JsonPathPiece};
use crate::writer::JsonWriter;

mod stream_reader;
// Re-export streaming implementation under `reader` module
pub use stream_reader::*;

type IoError = std::io::Error;

/// Type of a JSON value
#[derive(PartialEq, Eq, Clone, Copy, strum::Display, Debug)]
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

/// Line and column position
///
/// # Examples
/// Consider the following JSON document:
/// ```json
/// {
///   "a": null
/// }
/// ```
/// The position of `null` is:
/// - line: 1  
///   Line numbering starts at 0 and it is in the second line
/// - column: 7  
///   Column numbering starts at 0 and the `n` of `null` is the 8th character in that line,
///   respectively there are 7 characters in front of it
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct LinePosition {
    /// Line number, starting at 0
    ///
    /// The characters _CR_ (U+000D), _LF_ (U+000A) and _CR LF_ are considered line breaks. Other characters and
    /// escaped line breaks in member names and string values are not considered line breaks.
    pub line: u64,
    /// Character column within the current line, starting at 0
    ///
    /// For all Unicode characters this value is incremented only by one, regardless of whether some encodings
    /// such as UTF-8 might use more than one byte for the character, or whether encodings such as UTF-16
    /// might use two characters (a *surrogate pair*) to encode the character. Similarly the tab character
    /// (U+0009) is also considered a single character even though code editors might display it as if it
    /// consisted of more than one space character.
    pub column: u64,
}

impl Display for LinePosition {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "line {}, column {}", self.line, self.column)
    }
}

/// Position of the JSON reader in the JSON document
///
/// The position information can be used for troubleshooting malformed JSON or JSON data with an unexpected structure.
/// Which position information is available depends on the implementation of the JSON reader and its configuration.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct JsonReaderPosition {
    /// JSON path of the position
    ///
    /// The path describes which JSON array items and JSON object members to traverse to reach this position.  
    /// The last piece of the path cannot accurately point to the position in all cases because the position can be
    /// anywhere in the JSON document and in some cases this cannot be accurately or unambiguously described using
    /// a JSON path. The last path piece has the following meaning:
    ///
    /// - [`JsonPathPiece::ArrayItem`]: Index of the currently processed item, or index of the potential next item
    ///
    ///   For example the path `[..., ArrayItem(2)]` means that either the position is in front of a potential item
    ///   at index 2 (including the case where there are no subsequent items), or at the start or within the item at
    ///   index 2.
    ///
    ///   In general the index is incremented once a value in an array was fully consumed, which results in the
    ///   behavior described above.
    ///
    /// - [`JsonPathPiece::ObjectMember`]: Name of the previously read member, or name of the current member
    ///
    ///   For example the path `[..., ObjectMember("a")]` means that either the position is at the start or within
    ///   the value of the member with name "a" or before the end of the potential next member name (including the
    ///   case where there are no subsequent members).  
    ///   The special name `<?>` is used to indicate that a JSON object was started, but the name of the first member
    ///   has not been consumed yet.
    ///
    ///   In general the name in the JSON path is updated once the name of a member has been successfully read,
    ///   which results in the behavior described above.
    ///
    /// The path is `None` if the JSON reader implementation does not track the JSON path or if tracking the
    /// JSON path is [disabled in the `ReaderSettings`](ReaderSettings::track_path).
    ///
    /// For the exact position the [`line_pos`](Self::line_pos) and [`data_pos`](Self::data_pos) should be used.
    ///
    /// # Examples
    /// Consider the following JSON document:
    /// ```json
    /// {
    ///   "a": [1, null]
    /// }
    /// ```
    /// The position of `null` is `[ObjectMember("a"), ArrayItem(1)]`:
    /// - `ObjectMember("a")`: It is part of the value for the JSON object member named "a"
    /// - `ArrayItem(1)`: Within that value, which is a JSON array, it is at index 1 (numbering starts at 0)
    /* TODO: Maybe this should be `Cow<'a, JsonPath>`, but then need to propagate lifetime everywhere? */
    pub path: Option<Vec<JsonPathPiece>>,

    /// Line and column number
    ///
    /// This information is generally only provided by JSON reader implementations which read the JSON
    /// document as text in some way and where the concept of a line and column number makes sense.
    /// For other JSON reader implementations this might be `None`.
    pub line_pos: Option<LinePosition>,

    /// Position in the underlying data source
    ///
    /// The exact meaning depends on the JSON reader implementation and what type the underlying data
    /// has. The value starts at 0, representing the first data unit. It may either refer to the data
    /// unit which is currently processed (for example if it has an unexpected value) or the potential
    /// next data unit. For example for a JSON reader implementation based on [`std::io::Read`] the
    /// value might be the byte position.
    ///
    /// `None` if the JSON reader implementation does provide information about the data position.
    ///
    /// This value might not be equal to the amount of data consumed from the underlying data source
    /// in case the JSON reader buffers data internally which it has not processed yet.
    pub data_pos: Option<u64>,
}

impl Display for JsonReaderPosition {
    // Create display string depending on which of the Option values are present
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some(path) = &self.path {
            write!(f, "path '{}'", format_abs_json_path(path))?;

            if let Some(line_pos) = &self.line_pos {
                write!(f, ", {line_pos}")?;

                if let Some(data_pos) = &self.data_pos {
                    write!(f, " (data pos {data_pos})")?;
                }
            } else if let Some(data_pos) = &self.data_pos {
                write!(f, ", data pos {data_pos}")?;
            }
        } else if let Some(line_pos) = &self.line_pos {
            write!(f, "{line_pos}")?;

            if let Some(data_pos) = &self.data_pos {
                write!(f, " (data pos {data_pos})")?;
            }
        } else if let Some(data_pos) = &self.data_pos {
            write!(f, "data pos {data_pos}")?;
        } else {
            write!(f, "<location unavailable>")?;
        }

        Ok(())
    }
}

/// JSON syntax error
/*
 * This is a separate public struct because StringValueReader uses it when wrapping syntax error
 * inside std::io::Error. Otherwise, this should be private, and `ReaderError::SyntaxError` should
 * be a struct with these fields for consistency with the other error variants and for easier usage.
 */
#[derive(Error, PartialEq, Eq, Clone, Debug)]
#[error("JSON syntax error {kind} at {location}")]
pub struct JsonSyntaxError {
    /// Kind of the error
    pub kind: SyntaxErrorKind,
    /// Location where the error occurred in the JSON document
    pub location: JsonReaderPosition,
}

/// Describes why a syntax error occurred
#[non_exhaustive]
#[derive(PartialEq, Eq, Clone, Copy, strum::Display, Debug)]
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
#[derive(PartialEq, Eq, Clone, strum::Display, Debug)]
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
#[non_exhaustive]
#[derive(Error, Debug)]
// TODO: Rename to `JsonReaderError? current name might sound like this is only for errors from underlying `Read`
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
        location: JsonReaderPosition,
    },
    /// The JSON document had an unexpected structure
    ///
    /// This error occurs when trying to consume more elements than a JSON array or object has, or
    /// when trying to end a JSON array or object when there are still unprocessed elements in it.
    /// If these remaining elements should be ignored they can be skipped like this:
    /// ```
    /// # use struson::reader::*;
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
        location: JsonReaderPosition,
    },
    /// An unsupported JSON number value was encountered
    ///
    /// See [`ReaderSettings::restrict_number_values`] for more information.
    #[error("unsupported number value '{number}' at {location}")]
    UnsupportedNumberValue {
        /// The unsupported number value
        number: String,
        /// Location of the number value within the JSON document
        location: JsonReaderPosition,
    },
    /// An IO error occurred while trying to read from the underlying reader, or
    /// malformed UTF-8 data was encountered
    #[error("IO error '{error}' at (roughly) {location}")]
    IoError {
        /// The IO error which occurred
        error: IoError,
        /// Rough location where the error occurred within the JSON document
        ///
        /// The location might not be completely accurate. Since the IO error might have
        /// been returned by the underlying reader, it might not be related to the content
        /// of the JSON document. For example the location might still point to the beginning
        /// of the current JSON value while the IO error actually occurred multiple bytes
        /// ahead while fetching more data from the underlying reader.
        location: JsonReaderPosition,
    },
}

/// Error which occurred while calling [`JsonReader::transfer_to`]
#[derive(Error, Debug)]
pub enum TransferError {
    /// Error which occurred while reading from the JSON reader
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
///     - [`next_name`](Self::next_name), [`next_name_owned`](Self::next_name_owned): Reading the name of a JSON object member
///     - [`next_str`](Self::next_str), [`next_string`](Self::next_string), [`next_string_reader`](Self::next_string_reader): Reading a JSON string value
///     - [`next_number`](Self::next_number), [`next_number_as_str`](Self::next_number_as_str), [`next_number_as_string`](Self::next_number_as_string): Reading a JSON number value
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
/// # use struson::reader::*;
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
    /// This method does not guarantee that the peeked value is complete or valid; consuming it
    /// (with a separate method call) can return an error when malformed JSON data is detected.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::*;
    /// # let mut json_reader = JsonStreamReader::new("true".as_bytes());
    /// match json_reader.peek()? {
    ///     ValueType::Boolean => println!("A boolean: {}", json_reader.next_bool()?),
    ///     ValueType::String => println!("A string: {}", json_reader.next_str()?),
    ///     _ => panic!("Unexpected type"),
    /// }
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
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
    /* TODO: Rename to peek_value (or peek_value_type)? */
    fn peek(&mut self) -> Result<ValueType, ReaderError>;

    /// Begins consuming a JSON object
    ///
    /// The method [`has_next`](Self::has_next) can be used to check if there is a next object member.
    /// To consume a member first call [`next_name`](Self::next_name) or [`next_name_owned`](Self::next_name_owned)
    /// and afterwards one of the value reading methods such as [`next_number`](Self::next_number).
    /// At the end call [`end_object`](Self::end_object) to consume the closing bracket of the JSON object.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::*;
    /// let mut json_reader = JsonStreamReader::new(r#"{"a": 1, "b": 2}"#.as_bytes());
    /// json_reader.begin_object()?;
    ///
    /// // Prints "a: 1", "b: 2"
    /// while json_reader.has_next()? {
    ///     let name = json_reader.next_name_owned()?;
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
    /// # use struson::reader::*;
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
    /// # use struson::reader::*;
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
    /// # use struson::reader::*;
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
    /// # use struson::reader::*;
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

    /// Consumes and returns the name of the next JSON object member as `str`
    ///
    /// The name is returned as borrowed `str`. While that value is in scope, the Rust
    /// compiler might not permit using the JSON reader in any other way.
    /// If an owned `String` is needed, prefer [`next_name_owned`](Self::next_name_owned),
    /// that will most likely be more efficient than using this method to obtain a `str`
    /// and then converting that to an owned `String`.
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
    /// # use struson::reader::*;
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
    fn next_name(&mut self) -> Result<&'_ str, ReaderError>;

    /// Consumes and returns the name of the next JSON object member as `String`
    ///
    /// The name is returned as owned `String`. If a borrowed `str` suffices for
    /// your use case, prefer [`next_name`](Self::next_name), that will most likely
    /// be more efficient.
    ///
    /// See the documentation of [`next_name`](Self::next_name) for a detailed
    /// description of the behavior of reading a member name.
    fn next_name_owned(&mut self) -> Result<String, ReaderError>;

    /// Consumes and returns a JSON string value as `str`
    ///
    /// This method is only intended to consume string values, it cannot be used to consume
    /// JSON object member names. The method [`next_name`](Self::next_name) has to be used for that.
    ///
    /// The string value is returned as borrowed `str`. While that value is in scope, the Rust
    /// compiler might not permit using the JSON reader in any other way.
    /// If an owned `String` is needed, prefer [`next_string`](Self::next_string),
    /// that will most likely be more efficient than using this method to obtain a `str`
    /// and then converting that to an owned `String`.
    ///
    /// To avoid reading the complete string value into memory, the method [`next_string_reader`](Self::next_string_reader)
    /// can be used to obtain a reader which allows lazily reading the value. Especially for
    /// large string values this can be useful.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::*;
    /// let mut json_reader = JsonStreamReader::new(r#""text with \"quotes\"""#.as_bytes());
    /// assert_eq!("text with \"quotes\"", json_reader.next_str()?);
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
    fn next_str(&mut self) -> Result<&'_ str, ReaderError>;

    /// Consumes and returns a JSON string value as `String`
    ///
    /// The string value is returned as owned `String`. If a borrowed `str` suffices
    /// for your use case, prefer [`next_str`](Self::next_str), that will most likely
    /// be more efficient.
    ///
    /// See the documentation of [`next_str`](Self::next_str) for a detailed
    /// description of the behavior of reading a string value.
    fn next_string(&mut self) -> Result<String, ReaderError>;

    /// Provides a reader for lazily reading a JSON string value
    ///
    /// This method is mainly designed to process large string values in a memory efficient
    /// way. If that is not a concern the method [`next_str`](Self::next_str) should be used instead.
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
    /// # use struson::reader::*;
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
    /// JSON number should be preserved, the method [`next_number_as_str`](Self::next_number_as_str)
    /// can be used.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::*;
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
     * TODO: If FromStr returns an error, should include JsonReaderPosition for easier troubleshooting?
     *       Callers (such as Serde Deserializer number parsing implementation) would then not have to
     *       do this themselves
     */
    fn next_number<T: FromStr>(&mut self) -> Result<Result<T, T::Err>, ReaderError> {
        // Default implementation which should be suitable for most JsonReader implementations
        Ok(T::from_str(self.next_number_as_str()?))
    }

    /// Consumes and returns the string representation of a JSON number value as `str`
    ///
    /// This method is mainly intended for situations where parsing the number should be
    /// deferred to a later point, or the exact format of the JSON number should be preserved.
    /// However, this method nonetheless validates that the JSON number matches the format
    /// described by the JSON specification.
    ///
    /// The method [`next_number`](Self::next_number) can be used instead to parse the number directly in place.
    ///
    /// The number value is returned as borrowed `str`. While that value is in scope, the Rust
    /// compiler might not permit using the JSON reader in any other way.
    /// If an owned `String` is needed, prefer [`next_number_as_string`](Self::next_number_as_string),
    /// that will most likely be more efficient than using this method to obtain a `str`
    /// and then converting that to an owned `String`.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::*;
    /// let mut json_reader = JsonStreamReader::new("12.0e5".as_bytes());
    /// assert_eq!("12.0e5", json_reader.next_number_as_str()?);
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
    fn next_number_as_str(&mut self) -> Result<&'_ str, ReaderError>;

    /// Consumes and returns the string representation of a JSON number value as `String`
    ///
    /// The string value is returned as owned `String`. If a borrowed `str` suffices
    /// for your use case, prefer [`next_number_as_str`](Self::next_number_as_str), that
    /// will most likely be more efficient.
    ///
    /// See the documentation of [`next_number_as_str`](Self::next_number_as_str) for
    /// a detailed description of the behavior of reading a number value as string.
    fn next_number_as_string(&mut self) -> Result<String, ReaderError>;

    /// Consumes and returns a JSON boolean value
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::*;
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
    /// # use struson::reader::*;
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
    /// # use struson::reader::*;
    /// # use struson::reader::json_path::*;
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
    /// # use struson::reader::*;
    /// let mut json_reader = JsonStreamReader::new(r#"{"a": 1}"#.as_bytes());
    /// json_reader.begin_object()?;
    ///
    /// // Skip member name "a"
    /// json_reader.skip_name()?;
    ///
    /// assert_eq!("1", json_reader.next_number_as_str()?);
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
    /// methods (such as `next_str()`) but discarding their result.
    /// However, `skip_value` nonetheless also verifies that the skipped JSON data has valid syntax.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::*;
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
    /// Seeks to the specified relative JSON path in the JSON document by skipping all previous
    /// values. The JSON reader is expected to be positioned before the first value specified
    /// in the path. Once this method returns successfully the reader will be positioned
    /// before the last element specified by the path.
    ///
    /// For example for the JSON path `foo[2]` it will start consuming a JSON object, skipping members
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
    /// # use struson::reader::*;
    /// # use struson::reader::json_path::*;
    /// let mut json_reader = JsonStreamReader::new(
    ///     r#"{"bar": true, "foo": ["a", "b", "c"]}"#.as_bytes()
    /// );
    /// json_reader.seek_to(&json_path!["foo", 2])?;
    ///
    /// // Can now consume the value to which the call seeked to
    /// assert_eq!("c", json_reader.next_str()?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Errors
    /// (besides [`ReaderError::SyntaxError`] and [`ReaderError::IoError`])
    ///
    /// If the structure or the value types of the JSON document do not match the structure expected
    /// by the JSON path, either a [`ReaderError::UnexpectedStructure`] or a [`ReaderError::UnexpectedValueType`]
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
     * TODO: Rename this method? Name is based on file IO function `seek`, but not sure if "seek to"
     *   is a proper phrase in this context
     */
    fn seek_to(&mut self, rel_json_path: &JsonPath) -> Result<(), ReaderError> {
        // peek here to fail if reader is currently not expecting a value, even if `rel_json_path` is empty
        // and it would otherwise not be detected
        self.peek()?;

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
                                location: self.current_position(true),
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
                        if self.next_name()? == name {
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
                            location: self.current_position(true),
                        });
                    }
                }
            }
        }

        Ok(())
    }

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
    /// # use struson::reader::*;
    /// # use struson::reader::json_path::*;
    /// let mut json_reader = JsonStreamReader::new(
    ///     r#"{"bar": true, "foo": ["a", "b", "c"]}"#.as_bytes()
    /// );
    /// json_reader.seek_to(&json_path!["foo", 2])?;
    ///
    /// // Consume the value to which the call seeked to
    /// assert_eq!("c", json_reader.next_str()?);
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
    /// # use struson::reader::*;
    /// # use struson::reader::json_path::*;
    /// # use struson::writer::*;
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
    /// assert_eq!(r#"{"embedded":[1,2]}"#, String::from_utf8(writer)?);
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
    /// # use struson::reader::*;
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

    /// Gets the current position of this JSON reader within the JSON data
    ///
    /// The position can be used to enhance custom errors when building a parser on top
    /// of this JSON reader. `include_path` determines whether the [JSON path](JsonReaderPosition::path)
    /// should be included, assuming the JSON reader implementation supports providing
    /// this information (if it doesn't the path will be `None` regardless of `include_path`
    /// value). Including the JSON path can make the position information more useful
    /// for troubleshooting. However, if a caller frequently requests the position,
    /// for example to have it providently in case subsequent parsing fails, then it
    /// might improve performance to not include the path information.
    ///
    /// [Line](JsonReaderPosition::line_pos) and [data position](JsonReaderPosition::data_pos)
    /// are only specified if [`has_next`](Self::has_next) or [`peek`](Self::peek) have just
    /// been called, in which case their values point at the start of the next token. Otherwise
    /// their values can be anywhere between the previous token and the next token (if any).
    ///
    /// The position information makes no guarantee about the amount of data (e.g. number of
    /// bytes) consumed from the underlying data source. JSON reader implementations might
    /// buffer data which has not been processed yet.
    ///
    /// # Examples
    /// Let's assume an array of points encoded as JSON string in the format `x|y` should
    /// be parsed:
    ///
    /// ```
    /// # use struson::reader::*;
    /// let mut json_reader = JsonStreamReader::new(
    ///     r#"["1|2", "3|2", "8"]"#.as_bytes()
    /// );
    /// json_reader.begin_array()?;
    ///
    /// while json_reader.has_next()? {
    ///     let pos = json_reader.current_position(true);
    ///     let encoded_point = json_reader.next_str()?;
    ///
    /// #   #[allow(unused_variables)]
    ///     if let Some((x, y)) = encoded_point.split_once('|') {
    ///         // ...
    ///     } else {
    ///         // Includes the JSON reader position for easier troubleshooting
    ///         println!("Malformed point '{encoded_point}', at {pos}");
    ///     }
    /// }
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn current_position(&self, include_path: bool) -> JsonReaderPosition;
}

#[cfg(test)]
mod tests {
    use super::{json_path::JsonPathPiece, JsonReaderPosition, LinePosition};

    #[test]
    fn json_reader_location_display() {
        let path = Some(vec![
            JsonPathPiece::ArrayItem(1),
            JsonPathPiece::ObjectMember("name".to_owned()),
        ]);
        let line_pos = Some(LinePosition { line: 1, column: 2 });
        let data_pos = Some(3);

        let combinations = vec![
            ((None, None, None), "<location unavailable>"),
            ((None, None, data_pos), "data pos 3"),
            ((None, line_pos, None), "line 1, column 2"),
            ((None, line_pos, data_pos), "line 1, column 2 (data pos 3)"),
            ((path.clone(), None, None), "path '$[1].name'"),
            (
                (path.clone(), None, data_pos),
                "path '$[1].name', data pos 3",
            ),
            (
                (path.clone(), line_pos, None),
                "path '$[1].name', line 1, column 2",
            ),
            (
                (path.clone(), line_pos, data_pos),
                "path '$[1].name', line 1, column 2 (data pos 3)",
            ),
        ];

        for combination in combinations {
            let location_data = combination.0;
            let reader_location = JsonReaderPosition {
                path: location_data.0.clone(),
                line_pos: location_data.1,
                data_pos: location_data.2,
            };
            let display_string = reader_location.to_string();
            let expected_display_string = combination.1;
            assert_eq!(
                expected_display_string, display_string,
                "expected display string for {location_data:?}: {expected_display_string}"
            );
        }
    }
}
