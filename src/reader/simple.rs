//! JSON reader variant which is easier to use than [`JsonReader`]
//!
//! The main entrypoint is [`SimpleJsonReader`], all other structs and traits
//! are used by it for reading certain JSON value types.
//!
//! ----
//!
//! **🔬 Experimental**\
//! This API and the naming is currently experimental, please provide feedback [here](https://github.com/Marcono1234/struson/issues/34).
//! Any feedback is appreciated!

use std::{error::Error, io::Read, str::FromStr};

use self::{
    error_safe_reader::ErrorSafeJsonReader,
    multi_json_path::{MultiJsonPath, MultiJsonPathPiece},
};
use crate::{
    reader::{
        json_path::{JsonPath, JsonPathPiece},
        simple::error_safe_reader::create_dummy_error,
        JsonReader, JsonReaderPosition, JsonStreamReader, JsonSyntaxError, ReaderError,
        SyntaxErrorKind, TransferError, ValueType,
    },
    utf8,
    writer::JsonWriter,
};

/// Module for 'multi JSON path'
///
/// A 'multi JSON path' can point to multiple JSON values in a JSON document. It consists of zero or more
/// [`MultiJsonPathPiece`] elements which either represent JSON array items or JSON object members. These
/// pieces combined form the _path_ to the values in a JSON document.
///
/// This is not an implementation of the [JSONPath RFC 9535](https://www.rfc-editor.org/rfc/rfc9535) standard;
/// the implementation here uses a different syntax and only covers a subset of these features suitable
/// for the streaming JSON reader of this library. If you need more functionality, prefer a library
/// which fully implements the JSONPath standard.
///
/// If the path consists only of plain array indices and object member names, and therefore points to
/// exactly one value, the [`json_path` module](crate::reader::json_path) should be used instead.
///
/// The macro [`multi_json_path!`](multi_json_path::multi_json_path) can be used to create a JSON path in
/// a concise way. The path can then be used for [`ValueReader::read_seeked_multi`].
/*
 * Note: Multi JSON path is currently only provided for the Simple API but not for the Advanced API.
 * For the Simple API it can be easily verified that a single value was fully consumed; for the
 * Advanced API verifying this is more difficult. And the style of having a `FnMut` which is called
 * for all matched values also does not match the current style of the Advanced API.
 */
pub mod multi_json_path {
    /// A 'multi JSON path'
    ///
    /// A 'multi JSON path' as represented by this module are zero or more [`MultiJsonPathPiece`] elements.
    /// The macro [`multi_json_path!`] can be used to create a multi JSON path in a concise way.
    /* TODO: Check if it is somehow possible to implement Display for this */
    pub type MultiJsonPath = [MultiJsonPathPiece];

    /// A piece of a 'multi JSON path'
    ///
    /// A piece can either represent JSON array items or JSON object members.
    #[derive(PartialEq, Eq, Clone, Debug)]
    pub enum MultiJsonPathPiece {
        /// JSON array item at the specified index (starting at 0)
        ArrayItem(u32),
        /// All items of a JSON array
        AllArrayItems {
            /// Whether the array is allowed to be empty
            ///
            /// If `false` and an empty array is encountered, an error is returned. Regardless of this
            /// setting the JSON value must be present and must be a JSON array. If the value is missing
            /// or has a different value type, an error is returned.
            ///
            /// This only applies to the value matched by this path piece. If this path piece is not
            /// reached because a previous piece had no value, then this will not cause an error despite
            /// `allow_empty` being `false`.
            allow_empty: bool,
        },
        /// JSON object member with the specified name
        ObjectMember(String),
        /// Optional JSON object member with the specified name
        ///
        /// Indicates that the member (and any nested values) might not exist in a JSON object.
        /// This only covers the case where no member with the name exists; a member with explicit
        /// `null` JSON value will be considered present.
        OptionalObjectMember(String),
        /// All members of a JSON object, regardless of name
        ///
        /// If multiple members in a JSON object have the same name (for example `{"a": 1, "a": 2}`)
        /// this path piece matches all of them.
        AllObjectMembers {
            /// Whether the object is allowed to be empty
            ///
            /// If `false` and an empty object is encountered, an error is returned. Regardless of this
            /// setting the JSON value must be present and must be a JSON object. If the value is missing
            /// or has a different value type, an error is returned.
            ///
            /// This only applies to the value matched by this path piece. If this path piece is not
            /// reached because a previous piece had no value, then this will not cause an error despite
            /// `allow_empty` being `false`.
            allow_empty: bool,
        },
    }

    /// Creates a [`MultiJsonPathPiece::ArrayItem`] with the number as index
    impl From<u32> for MultiJsonPathPiece {
        fn from(v: u32) -> Self {
            MultiJsonPathPiece::ArrayItem(v)
        }
    }

    /// Creates a [`MultiJsonPathPiece::ObjectMember`] with the string as member name
    impl From<String> for MultiJsonPathPiece {
        fn from(v: String) -> Self {
            MultiJsonPathPiece::ObjectMember(v)
        }
    }

    /// Creates a [`MultiJsonPathPiece::ObjectMember`] with the string as member name
    impl From<&str> for MultiJsonPathPiece {
        fn from(v: &str) -> Self {
            MultiJsonPathPiece::ObjectMember(v.to_string())
        }
    }

    // TODO: Is there a built-in trait for this? `Into<String>` and `ToString` might allow too many unrelated types,
    //   and calling `expr.to_owned()` in the macro creates a redundant clone for `String::to_owned`
    #[doc(hidden)]
    pub trait __IntoString {
        fn into_string(self) -> String;
    }
    // Covers the same types supported for `MultiJsonPathPiece::ObjectMember`
    impl __IntoString for String {
        fn into_string(self) -> String {
            self
        }
    }
    impl __IntoString for &str {
        fn into_string(self) -> String {
            self.to_owned()
        }
    }

    /// Actual implementation of `multi_json_path!`
    /*
     * This is a separate macro because:
     * - It allows omitting all the verbose rules from the rustdoc
     * - It allows specifying internal rules without having to rely on verbose patterns such
     *   as 'Internal Rules' (https://veykril.github.io/tlborm/decl-macros/patterns/internal-rules.html)
     */
    #[doc(hidden)]
    #[macro_export] // must be exported, otherwise the public `multi_json_path!` cannot use it
    macro_rules! __multi_json_path_impl {
        // 'Incremental TT Muncher', see https://veykril.github.io/tlborm/decl-macros/patterns/tt-muncher.html
        // Based partially on serde_json's `json!` macro implementation

        // First cover special syntax `[*]`, `[+]`, `{*}` and `[+]`
        ( [$($pieces:expr,)*] [*] $($rest:tt)* ) => {
            $crate::__multi_json_path_impl!(
                [$($pieces,)* $crate::reader::simple::multi_json_path::MultiJsonPathPiece::AllArrayItems { allow_empty: true }] $($rest)*
            )
        };
        ( [$($pieces:expr,)*] [+] $($rest:tt)* ) => {
            $crate::__multi_json_path_impl!(
                [$($pieces,)* $crate::reader::simple::multi_json_path::MultiJsonPathPiece::AllArrayItems { allow_empty: false }] $($rest)*
            )
        };
        ( [$($pieces:expr,)*] {*} $($rest:tt)* ) => {
            $crate::__multi_json_path_impl!(
                [$($pieces,)* $crate::reader::simple::multi_json_path::MultiJsonPathPiece::AllObjectMembers { allow_empty: true }] $($rest)*
            )
        };
        ( [$($pieces:expr,)*] {+} $($rest:tt)* ) => {
            $crate::__multi_json_path_impl!(
                [$($pieces,)* $crate::reader::simple::multi_json_path::MultiJsonPathPiece::AllObjectMembers { allow_empty: false }] $($rest)*
            )
        };

        // Then cover optional object member piece `?name`
        // Needs two rules because macro_rules requires that `,` must follow `expr` here
        ( [$($pieces:expr,)*] ?$piece:expr, $($rest:tt)* ) => {
            $crate::__multi_json_path_impl!(
                // Include trailing `,` to disallow duplicated commas
                [$($pieces,)* $crate::reader::simple::multi_json_path::MultiJsonPathPiece::OptionalObjectMember($crate::reader::simple::multi_json_path::__IntoString::into_string($piece)),] $($rest)*
            )
        };
        // Last piece
        ( [$($pieces:expr,)*] ?$piece:expr) => {
            $crate::__multi_json_path_impl!(
                [$($pieces,)* $crate::reader::simple::multi_json_path::MultiJsonPathPiece::OptionalObjectMember($crate::reader::simple::multi_json_path::__IntoString::into_string($piece)),]
            )
        };

        // Then cover regular array item and object member pieces
        // Needs two rules because macro_rules requires that `,` must follow `expr` here
        ( [$($pieces:expr,)*] $piece:expr, $($rest:tt)* ) => {
            $crate::__multi_json_path_impl!(
                // Include trailing `,` to disallow duplicated commas
                [$($pieces,)* $crate::reader::simple::multi_json_path::MultiJsonPathPiece::from($piece),] $($rest)*
            )
        };
        // Last piece
        ( [$($pieces:expr,)*] $piece:expr) => {
            $crate::__multi_json_path_impl!(
                [$($pieces,)* $crate::reader::simple::multi_json_path::MultiJsonPathPiece::from($piece),]
            )
        };

        // Leading comma (only if there is at least one piece, and no trailing comma yet)
        ( [$($pieces:expr),+] , $($rest:tt)*) => {
            $crate::__multi_json_path_impl!(
                // Include trailing `,` to disallow duplicated commas
                [$($pieces),+ ,] $($rest)*
            )
        };

        // Finish
        ( [] ) => {
            // Specify the type to avoid it being used by accident as an empty array of any type
            [] as [$crate::reader::simple::multi_json_path::MultiJsonPathPiece; 0]
        };
        ( [$($pieces:expr),+ $(,)?] ) => {
            [$($pieces),+]
        };
    }

    /*
     * TODO: Ideally in the future not expose this at the crate root but only from the `multi_json_path` module
     *   however, that is apparently not easily possible yet.
     *   Therefore for now hide this macro and re-export it with the desired name below, see
     *   https://internals.rust-lang.org/t/pub-on-macro-rules/19358/16
     */
    #[doc(hidden)]
    #[macro_export]
    macro_rules! __multi_json_path {
        ( $($path:tt)* ) => {
            $crate::__multi_json_path_impl!([] $($path)*)
        };
    }

    /// Creates a 'multi JSON path' from path pieces, separated by commas
    ///
    /// The arguments to this macro represent the path pieces:
    ///
    /// | Argument | Path piece |
    /// | - | - |
    /// | number of type `u32` | [`ArrayItem`](MultiJsonPathPiece::ArrayItem) |
    /// | string | [`ObjectMember`](MultiJsonPathPiece::ObjectMember) |
    /// | '`?`string' | [`OptionalObjectMember`](MultiJsonPathPiece::OptionalObjectMember) |
    /// | '`[*]`' | [`AllArrayItems { allow_empty: true }`](MultiJsonPathPiece::AllArrayItems) |
    /// | '`[+]`' | [`AllArrayItems { allow_empty: false }`](MultiJsonPathPiece::AllArrayItems) |
    /// | '`{*}`' | [`AllObjectMembers { allow_empty: true }`](MultiJsonPathPiece::AllObjectMembers) |
    /// | '`{+}`' | [`AllObjectMembers { allow_empty: false }`](MultiJsonPathPiece::AllObjectMembers) |
    ///
    /// Providing no arguments creates an empty path without any path pieces.
    ///
    /// # Examples
    /// Let's assume you have the following JSON data representing a list of books where
    /// some of them have received awards, stored in the optional nested `awards` array.
    /// ```json
    /// {
    ///   "books": [
    ///     {
    ///       "title": "A normal day in the life of an ant",
    ///       "awards": [
    ///         "Best Thriller",
    ///         "Best Short Story"
    ///       ]
    ///     },
    ///     {
    ///       "title": "Tired of Potatoes"
    ///     }
    ///   ]  
    /// }
    /// ```
    ///
    /// Then the following multi JSON path can be used to match all awards any book has
    /// received:
    /// ```
    /// # use struson::reader::simple::multi_json_path::*;
    /// # use struson::reader::simple::multi_json_path::MultiJsonPathPiece::*;
    /// let json_path = multi_json_path![
    ///     "books",
    ///     [*], // match all books
    ///     ?"awards", // match the optional "awards" member
    ///     [+], // match all awards (requiring non-empty array)
    /// ];
    ///
    /// assert_eq!(
    ///     json_path,
    ///     [
    ///         ObjectMember("books".to_owned()),
    ///         AllArrayItems { allow_empty: true },
    ///         OptionalObjectMember("awards".to_owned()),
    ///         AllArrayItems { allow_empty: false },
    ///     ]
    /// );
    /// ```
    /* Re-export the macro to be available under the `struson::reader::simple::multi_json_path` module path */
    #[doc(inline)]
    pub use __multi_json_path as multi_json_path;

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn macro_multi_json_path() {
            assert_eq!(multi_json_path![], []);
            // Make sure the type is correct and it can be compared with a &MultiJsonPath
            assert_ne!(
                multi_json_path![],
                &[MultiJsonPathPiece::ArrayItem(1)] as &MultiJsonPath
            );
            assert_eq!(multi_json_path![3], [MultiJsonPathPiece::ArrayItem(3)]);
            // Make sure the type is correct and it can be compared with a &MultiJsonPath
            assert_eq!(
                multi_json_path![3],
                &[MultiJsonPathPiece::ArrayItem(3)] as &MultiJsonPath
            );
            assert_eq!(
                multi_json_path!["a"],
                [MultiJsonPathPiece::ObjectMember("a".to_owned())]
            );
            assert_eq!(
                multi_json_path!["a".to_owned()],
                [MultiJsonPathPiece::ObjectMember("a".to_owned())]
            );
            assert_eq!(
                // Trailing comma
                multi_json_path!["a",],
                [MultiJsonPathPiece::ObjectMember("a".to_owned())]
            );
            assert_eq!(
                // Trailing comma
                multi_json_path!["a", 1,],
                [
                    MultiJsonPathPiece::ObjectMember("a".to_owned()),
                    MultiJsonPathPiece::ArrayItem(1),
                ]
            );
            assert_eq!(
                multi_json_path!["outer", 1, "inner".to_owned(), 2],
                [
                    MultiJsonPathPiece::ObjectMember("outer".to_owned()),
                    MultiJsonPathPiece::ArrayItem(1),
                    MultiJsonPathPiece::ObjectMember("inner".to_owned()),
                    MultiJsonPathPiece::ArrayItem(2),
                ]
            );

            assert_eq!(
                multi_json_path![?"a"],
                [MultiJsonPathPiece::OptionalObjectMember("a".to_owned())]
            );
            assert_eq!(
                multi_json_path![?"a".to_owned()],
                [MultiJsonPathPiece::OptionalObjectMember("a".to_owned())]
            );
            // Trailing comma
            assert_eq!(
                multi_json_path![?"a",],
                [MultiJsonPathPiece::OptionalObjectMember("a".to_owned())]
            );
            assert_eq!(
                multi_json_path![?"a", "b"],
                [
                    MultiJsonPathPiece::OptionalObjectMember("a".to_owned()),
                    MultiJsonPathPiece::ObjectMember("b".to_owned()),
                ]
            );

            assert_eq!(
                multi_json_path![[*]],
                [MultiJsonPathPiece::AllArrayItems { allow_empty: true }]
            );
            // Trailing comma
            assert_eq!(
                multi_json_path![[*],],
                [MultiJsonPathPiece::AllArrayItems { allow_empty: true }]
            );
            assert_eq!(
                multi_json_path![1, [*]],
                [
                    MultiJsonPathPiece::ArrayItem(1),
                    MultiJsonPathPiece::AllArrayItems { allow_empty: true },
                ]
            );
            // Trailing comma
            assert_eq!(
                multi_json_path![1, [*],],
                [
                    MultiJsonPathPiece::ArrayItem(1),
                    MultiJsonPathPiece::AllArrayItems { allow_empty: true },
                ]
            );
            assert_eq!(
                multi_json_path![1, [*], 1],
                [
                    MultiJsonPathPiece::ArrayItem(1),
                    MultiJsonPathPiece::AllArrayItems { allow_empty: true },
                    MultiJsonPathPiece::ArrayItem(1),
                ]
            );
            assert_eq!(
                multi_json_path![[+]],
                [MultiJsonPathPiece::AllArrayItems { allow_empty: false }]
            );

            assert_eq!(
                multi_json_path![{*}],
                [MultiJsonPathPiece::AllObjectMembers { allow_empty: true }]
            );
            // Trailing comma
            assert_eq!(
                multi_json_path![{*},],
                [MultiJsonPathPiece::AllObjectMembers { allow_empty: true }]
            );
            assert_eq!(
                multi_json_path![1, {*}],
                [
                    MultiJsonPathPiece::ArrayItem(1),
                    MultiJsonPathPiece::AllObjectMembers { allow_empty: true },
                ]
            );
            // Trailing comma
            assert_eq!(
                multi_json_path![1, {*},],
                [
                    MultiJsonPathPiece::ArrayItem(1),
                    MultiJsonPathPiece::AllObjectMembers { allow_empty: true },
                ]
            );
            assert_eq!(
                multi_json_path![1, {*}, 1],
                [
                    MultiJsonPathPiece::ArrayItem(1),
                    MultiJsonPathPiece::AllObjectMembers { allow_empty: true },
                    MultiJsonPathPiece::ArrayItem(1),
                ]
            );
            assert_eq!(
                multi_json_path![{+}],
                [MultiJsonPathPiece::AllObjectMembers { allow_empty: false }]
            );

            assert_eq!(
                multi_json_path![[*], [+], {*}, {+}, 1],
                [
                    MultiJsonPathPiece::AllArrayItems { allow_empty: true },
                    MultiJsonPathPiece::AllArrayItems { allow_empty: false },
                    MultiJsonPathPiece::AllObjectMembers { allow_empty: true },
                    MultiJsonPathPiece::AllObjectMembers { allow_empty: false },
                    MultiJsonPathPiece::ArrayItem(1),
                ]
            );
        }
    }
}

/// Reader for a JSON value
pub trait ValueReader<J: JsonReader> {
    /// Peeks at the type of the next JSON value, without consuming it
    fn peek_value(&mut self) -> Result<ValueType, ReaderError>;

    /// Consumes a JSON null value
    fn read_null(self) -> Result<(), ReaderError>;

    /// Consumes and returns a JSON boolean value
    fn read_bool(self) -> Result<bool, ReaderError>;

    /// Consumes a JSON string value as borrowed `str`
    ///
    /// The function `f` is called with the read JSON string value as argument.
    ///
    /// To read a string value as owned `String` use [`read_string`](Self::read_string).\
    /// To read a large string value in a streaming way, use [`read_string_with_reader`](Self::read_string_with_reader).
    /*
     * Note: Ideally would return a `&str`, but that does not seem to be possible because `self`
     * is consumed. And for some of the `ValueReader` implementations below this would probably
     * also not work because they call additional methods after reading the value, e.g. `consume_trailing_whitespace()`
     */
    fn read_str<T>(
        self,
        f: impl FnOnce(&str) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>>;

    /// Consumes and returns a JSON string value as owned `String`
    ///
    /// To read a string value as borrowed `str` use [`read_str`](Self::read_str).\
    /// To read a large string value in a streaming way, use [`read_string_with_reader`](Self::read_string_with_reader).
    fn read_string(self) -> Result<String, ReaderError>;

    /// Consumes a JSON string using a [`Read`]
    ///
    /// The function `f` is called with a reader as argument which allows reading the JSON string
    /// value. Escape sequences will be automatically converted to the corresponding characters. If
    /// the function returns `Ok` but did not consume all bytes of the string value, the remaining
    /// bytes will be skipped automatically.
    ///
    /// This method is mainly intended for reading large JSON string values in a streaming way;
    /// for short string values prefer [`read_str`](Self::read_str) or [`read_string`](Self::read_string).
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// # use std::io::Read;
    /// let json_reader = SimpleJsonReader::new("\"text with \\\" quote\"".as_bytes());
    /// json_reader.read_string_with_reader(|mut string_reader| {
    ///     let mut buf = [0_u8; 1];
    ///     while string_reader.read(&mut buf)? > 0 {
    ///         println!("Read byte: {}", buf[0]);
    ///     }
    ///     Ok(())
    /// })?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Reader errors
    /// When the underlying reader encounters an error, or when malformed JSON data is encountered
    /// the reader will return a [`std::io::Error`].
    ///
    /// The error behavior of the string reader differs from the guarantees made by [`Read`]:
    /// - if an error is returned there are no guarantees about if or how many data has been
    ///   consumed from the underlying data source and been stored in the provided `buf`
    /// - if an error occurs, processing should be aborted, regardless of the kind of the error;
    ///   trying to use the string reader or the original JSON reader afterwards will lead
    ///   to unspecified behavior
    fn read_string_with_reader<T>(
        self,
        f: impl FnOnce(StringValueReader<'_>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>>;

    /// Consumes and returns a JSON number value
    ///
    /// The result is either the parsed number or the parse error. It might be necessary to
    /// help the Rust compiler a bit by explicitly specifying the number type in case it cannot
    /// be inferred automatically.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// let json_reader = SimpleJsonReader::new("12".as_bytes());
    /// let number: u64 = json_reader.read_number()??;
    /// assert_eq!(number, 12);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn read_number<T: FromStr>(self) -> Result<Result<T, T::Err>, ReaderError>;

    /// Consumes and returns the string representation of a JSON number value
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// let json_reader = SimpleJsonReader::new("1.2e3".as_bytes());
    /// let number_string = json_reader.read_number_as_string()?;
    /// assert_eq!(number_string, "1.2e3");
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn read_number_as_string(self) -> Result<String, ReaderError>;

    /// Deserializes a Serde [`Deserialize`](serde::de::Deserialize) from the next value
    ///
    /// This method is part of the optional Serde integration feature, see the
    /// [`serde` module](crate::serde) of this crate for more information.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// # use serde::*;
    /// let json_reader = SimpleJsonReader::new(
    ///     r#"{"text": "some text", "number": 5}"#.as_bytes()
    /// );
    ///
    /// #[derive(Deserialize, PartialEq, Debug)]
    /// struct MyStruct {
    ///     text: String,
    ///     number: u64,
    /// }
    ///
    /// let value: MyStruct = json_reader.read_deserialize()?;
    /// assert_eq!(
    ///     value,
    ///     MyStruct { text: "some text".to_owned(), number: 5 }
    /// );
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Security
    /// Since JSON data can have an arbitrary structure and can contain arbitrary
    /// data, care must be taken when processing untrusted data. See the documentation
    /// of [`JsonReaderDeserializer`](crate::serde::JsonReaderDeserializer) for
    /// security considerations.
    #[cfg(feature = "serde")]
    fn read_deserialize<'de, D: serde::de::Deserialize<'de>>(
        self,
    ) -> Result<D, crate::serde::DeserializerError>;

    /// Skips the next JSON value
    ///
    /// If the value is a JSON array or object, all the nested values will be skipped as well.
    /// This method is usually more efficient than reading the next JSON value using one of
    /// the other methods, but discarding the read result afterwards.
    fn skip_value(self) -> Result<(), ReaderError>;

    /// Consumes a JSON array
    ///
    /// This method is useful when arrays of fixed size or with heterogenous item types are read;
    /// otherwise prefer [`read_array_items`](Self::read_array_items).
    ///
    /// If the exact size is not known in advance, [`ArrayReader::has_next`] can be used to
    /// check if there are more items in the JSON array. If the value types are not known in
    /// advance, [`ArrayReader::peek_value`](ValueReader::peek_value) can be used to peek at
    /// the next item (optionally calling `has_next` before to make sure there is actually a
    /// next item).
    ///
    /// If the function `f` returns `Ok` it must have consumed all array items, either by
    /// reading them or by calling [`ArrayReader::skip_value`](ValueReader::skip_value) until
    /// there are no more items (can be checked using [`ArrayReader::has_next`]). Otherwise
    /// an error is returned.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// let json_reader = SimpleJsonReader::new("[1, 2, 3]".as_bytes());
    /// let point: (u64, u64, u64) = json_reader.read_array(|array_reader| {
    ///     let x = array_reader.read_number()??;
    ///     let y = array_reader.read_number()??;
    ///     let z = array_reader.read_number()??;
    ///     Ok((x, y, z))
    /// })?;
    /// assert_eq!(point, (1, 2, 3));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn read_array<T>(
        self,
        f: impl FnOnce(&mut ArrayReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>>;

    /// Consumes a JSON array and all of its items
    ///
    /// This method is useful when arrays with varying size and homogenous item type are read;
    /// otherwise prefer [`read_array`](Self::read_array).
    ///
    /// The function `f` is called repeatedly for all items of the JSON array, if any.
    ///
    /// If the function returns `Ok` but did not consume the array item, either by
    /// reading it (e.g. using [`read_bool`](Self::read_bool)) or by using [`skip_value`](Self::skip_value),
    /// the item will be skipped automatically.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// let json_reader = SimpleJsonReader::new(r#"["a", "short", "example"]"#.as_bytes());
    /// let mut words = Vec::<String>::new();
    /// json_reader.read_array_items(|item_reader| {
    ///     let word = item_reader.read_string()?;
    ///     words.push(word);
    ///     Ok(())
    /// })?;
    /// assert_eq!(words, vec!["a", "short", "example"]);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn read_array_items(
        self,
        mut f: impl FnMut(SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>>
    where
        Self: Sized,
    {
        self.read_array(|array_reader| {
            while array_reader.has_next()? {
                read_value(array_reader.json_reader, &mut f)?;
            }
            Ok(())
        })
    }

    /// Consumes a JSON object and all of its members, reading names as borrowed `str`
    ///
    /// The function `f` is called repeatedly for all members of the JSON object, if any. It
    /// takes a [`MemberReader`] as argument which allows reading the name and the value of the
    /// member.
    ///
    /// If the function returns `Ok` but did not read the name or the value of the member, then
    /// name or value will be skipped automatically.
    ///
    /// If the name is needed as owned `String`, then [`read_object_owned_names`](Self::read_object_owned_names)
    /// should be used instead.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// let json_reader = SimpleJsonReader::new(r#"{"a": 1, "b": 2}"#.as_bytes());
    ///
    /// let mut a: Option<u32> = None;
    /// json_reader.read_object_borrowed_names(|mut member_reader| {
    ///     let name = member_reader.read_name()?;
    ///     match name {
    ///         "a" => a = Some(member_reader.read_number()??),
    ///         _ => {
    ///             // ignore member value
    ///         }
    ///     }
    ///     Ok(())
    /// })?;
    /// assert_eq!(a, Some(1));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn read_object_borrowed_names(
        self,
        f: impl FnMut(MemberReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>>;

    /// Consumes a JSON object and all of its members, reading names as owned `String`
    ///
    /// The function `f` is called repeatedly for all members of the JSON object, if any. It takes
    /// the member name as first argument and a [`SingleValueReader`] for reading the member value
    /// as second argument.
    ///
    /// If the function returns `Ok` but did not consume the value of the member, either by
    /// reading it (e.g. using [`read_bool`](Self::read_bool)) or by using [`skip_value`](Self::skip_value),
    /// the value will be skipped automatically.
    ///
    /// If it suffices to have the name as borrowed `str`, then [`read_object_borrowed_names`](Self::read_object_borrowed_names)
    /// should be used instead.
    ///
    /// # Examples
    /// ```
    /// # use std::collections::HashMap;
    /// # use struson::reader::simple::*;
    /// let json_reader = SimpleJsonReader::new(r#"{"a": 1, "b": 2}"#.as_bytes());
    /// let mut map = HashMap::<String, u64>::new();
    /// json_reader.read_object_owned_names(|name, value_reader| {
    ///     let member_value = value_reader.read_number()??;
    ///     map.insert(name, member_value);
    ///     Ok(())
    /// })?;
    ///
    /// assert_eq!(
    ///     map,
    ///     HashMap::from([
    ///         ("a".to_owned(), 1),
    ///         ("b".to_owned(), 2),
    ///     ])
    /// );
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn read_object_owned_names(
        self,
        f: impl FnMut(String, SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>>;

    /// Seeks to a value and consumes it
    ///
    /// This method first seeks to the location specified by `path` as described by
    /// [`SimpleJsonReader::seek_to`], then calls the function `f` to consume the value.
    ///
    /// If the path matches a value, the function `f` will be called exactly once.
    /// Otherwise, if the structure of the JSON data does not match the path, for example
    /// when the JSON data contains an array but the path expects an object, an error
    /// is returned and `f` is not called.
    ///
    /// If the function `f` returns `Ok` but did not consume the value, it will be skipped
    /// automatically. After the function has been called this method traverses back to
    /// the original nesting level, therefore acting as if it only consumed one value
    /// (and its nested values) at that level.
    ///
    /// For seeking to and reading multiple values use [`read_seeked_multi`](Self::read_seeked_multi).
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// # use struson::reader::json_path::*;
    /// let json_reader = SimpleJsonReader::new(
    ///     r#"[{"bar": true, "foo": ["a", "b", "c"]}, "next"]"#.as_bytes()
    /// );
    ///
    /// json_reader.read_array(|array_reader| {
    ///     // First seek to the "foo" member, then within its value seek to the item at index 1
    ///     array_reader.read_seeked(&json_path!["foo", 1], |value_reader| {
    ///         // Read the value where the reader seeked to
    ///         assert_eq!(value_reader.read_string()?, "b");
    ///         Ok(())
    ///     })?;
    ///     
    ///     // Afterwards can continue reading at original nesting level
    ///     assert_eq!(array_reader.read_string()?, "next");
    ///     Ok(())
    /// })?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    /*
     * Note: Functionality-wise `read_seeked` might not be needed and a user could instead call
     * `read_seeked_multi` with a plain path without any wildcards. However, `read_seeked` has
     * these advantages:
     * - It guarantees that it either calls `f` or returns an error; for `read_seeked_multi` you
     *   would have to deduce that from the given path or use `at_least_one_match = true`
     * - It supports an `FnOnce` (instead of just an `FnMut`), and returning a result from `f`
     */
    fn read_seeked<T>(
        self,
        path: &JsonPath,
        f: impl FnOnce(SingleValueReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>>;

    /// Seeks to multiple values and consumes them
    ///
    /// Based on the given `path` this method seeks to all matching values, if any, and calls the
    /// function `f` repeatedly for reading each value. If the function returns `Ok` but did not
    /// consume the value, it will be skipped automatically.
    ///
    /// Depending on what pieces the path consists of, it can match any number of values, including
    /// none. The `at_least_one_match` argument determines the behavior of this method in case the
    /// path matches no values. If `true` an error is returned; this can for example be useful when
    /// a JSON object member is [optional](MultiJsonPathPiece::OptionalObjectMember) but for multiple
    /// of such objects at least one is expected to have the member. If `false` no error is returned
    /// but `f` is also not called. This does not override the behavior for path pieces which themself
    /// require at least one match, such as [`AllArrayItems { allow_empty: false }`](MultiJsonPathPiece::AllArrayItems).
    ///
    /// For [`ObjectMember`](MultiJsonPathPiece::ObjectMember) and [`OptionalObjectMember`](MultiJsonPathPiece::OptionalObjectMember)
    /// pieces if multiple members in a JSON object have the same name (for example `{"a": 1, "a": 2}`)
    /// this method will only seek to the first occurrence in that object ignoring the others.
    ///
    /// Once this method returns, the reader is at the original nesting level again and can continue
    /// consuming values there. Calling this method therefore acts as if it only consumed one value
    /// (and its nested values) at the that level.
    ///
    /// If the structure of the JSON data does not match the path, for example the JSON data contains
    /// an array but the path expects an object, an error is returned.
    ///
    /// For seeking to and reading a single value at a fixed path prefer [`read_seeked`](Self::read_seeked).
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// # use struson::reader::simple::multi_json_path::*;
    /// let json = r#"{
    ///     "users": [
    ///         {"name": "John", "age": 32},
    ///         {"name": "Jane", "age": 41}
    ///     ]
    /// }"#;
    /// let json_reader = SimpleJsonReader::new(json.as_bytes());
    ///
    /// let mut ages = Vec::<u32>::new();
    /// // Select the ages of all users
    /// let json_path = multi_json_path!["users", [*], "age"];
    /// json_reader.read_seeked_multi(&json_path, false, |value_reader| {
    ///     let age = value_reader.read_number()??;
    ///     ages.push(age);
    ///     Ok(())
    /// })?;
    /// assert_eq!(ages, vec![32, 41]);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn read_seeked_multi(
        self,
        path: &MultiJsonPath,
        at_least_one_match: bool,
        f: impl FnMut(SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>>;
}

fn read_array<J: JsonReader, T>(
    json_reader: &mut ErrorSafeJsonReader<J>,
    f: impl FnOnce(&mut ArrayReader<'_, J>) -> Result<T, Box<dyn Error>>,
) -> Result<T, Box<dyn Error>> {
    json_reader.begin_array()?;
    let mut array_reader = ArrayReader { json_reader };
    let result = f(&mut array_reader)?;
    json_reader.end_array()?;
    Ok(result)
}

fn read_object_borrowed_names<J: JsonReader>(
    json_reader: &mut ErrorSafeJsonReader<J>,
    mut f: impl FnMut(MemberReader<'_, J>) -> Result<(), Box<dyn Error>>,
) -> Result<(), Box<dyn Error>> {
    json_reader.begin_object()?;
    while json_reader.has_next()? {
        let mut consumed_name = false;
        let mut consumed_value = false;
        let member_reader = MemberReader {
            json_reader,
            consumed_name: &mut consumed_name,
            consumed_value: &mut consumed_value,
        };
        f(member_reader)?;
        // If the function did not consume the member name or value, skip them
        if !consumed_name {
            json_reader.skip_name()?;
        }
        if !consumed_value {
            json_reader.skip_value()?;
        }
    }
    json_reader.end_object()?;
    Ok(())
}

fn read_object_owned_names<J: JsonReader>(
    json_reader: &mut ErrorSafeJsonReader<J>,
    mut f: impl FnMut(String, SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
) -> Result<(), Box<dyn Error>> {
    json_reader.begin_object()?;
    while json_reader.has_next()? {
        let name = json_reader.next_name_owned()?;
        let mut consumed_value = false;
        let member_value_reader = SingleValueReader {
            json_reader,
            consumed_value: &mut consumed_value,
        };
        f(name, member_value_reader)?;
        // If the function did not consume the value, skip it
        if !consumed_value {
            json_reader.skip_value()?;
        }
    }
    json_reader.end_object()?;
    Ok(())
}

fn read_string_with_reader<J: JsonReader, T>(
    json_reader: &mut ErrorSafeJsonReader<J>,
    f: impl FnOnce(StringValueReader<'_>) -> Result<T, Box<dyn Error>>,
) -> Result<T, Box<dyn Error>> {
    let mut delegate = json_reader.next_string_reader()?;
    let string_reader: StringValueReader<'_> = StringValueReader {
        delegate: &mut delegate as &mut dyn Read,
    };
    let result = f(string_reader)?;

    // Check if there is error which was not propagated by function
    if let Some(error) = delegate.error {
        return Err(error.rough_clone().into());
    }

    // Skip remaining bytes, if any
    // First check with small buffer if there are any bytes to skip
    // TODO: Should this retry on `ErrorKind::Interrupted`?
    if delegate.read(&mut [0_u8; utf8::MAX_BYTES_PER_CHAR])? > 0 {
        // Then use larger buffer for skipping
        let mut buf = [0_u8; 512];

        while delegate.read(&mut buf)? > 0 {
            // Do nothing
        }
    }

    Ok(result)
}

/// Reads a value with `f`, implicitly skipping the value if `f` did not consume it
fn read_value<J: JsonReader, T>(
    json_reader: &mut ErrorSafeJsonReader<J>,
    f: impl FnOnce(SingleValueReader<'_, J>) -> Result<T, Box<dyn Error>>,
) -> Result<T, Box<dyn Error>> {
    let mut consumed_value = false;
    let value_reader = SingleValueReader {
        json_reader,
        consumed_value: &mut consumed_value,
    };

    let result = f(value_reader)?;
    // If the function did not consume the value, skip it
    if !consumed_value {
        json_reader.skip_value()?;
    }
    Ok(result)
}

fn read_seeked<J: JsonReader, T>(
    json_reader: &mut ErrorSafeJsonReader<J>,
    path: &JsonPath,
    f: impl FnOnce(SingleValueReader<'_, J>) -> Result<T, Box<dyn Error>>,
) -> Result<T, Box<dyn Error>> {
    json_reader.seek_to(path)?;
    let result = read_value(json_reader, f)?;
    json_reader.seek_back(path)?;
    Ok(result)
}

fn read_seeked_multi<J: JsonReader>(
    json_reader: &mut ErrorSafeJsonReader<J>,
    original_path: &MultiJsonPath,
    require_at_least_one_match: bool,
    mut f: impl FnMut(SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
) -> Result<(), Box<dyn Error>> {
    // Special case for empty path because the logic below only handles non-empty paths
    if original_path.is_empty() {
        return read_value(json_reader, &mut f);
    }

    enum PartialPath {
        JsonPath(Vec<JsonPathPiece>),
        AllArrayItems { allow_empty: bool },
        OptionalObjectMember(String),
        AllObjectMembers { allow_empty: bool },
    }

    /// Converts the path to an internal representation where 'plain' path pieces (i.e. no wildcards, ...)
    /// are merged together to a regular JSON path
    fn convert_path(path: &MultiJsonPath) -> Vec<PartialPath> {
        let mut converted_path = Vec::<PartialPath>::new();
        let mut current_section = None;

        for piece in path {
            match piece {
                MultiJsonPathPiece::ArrayItem(index) => {
                    let current_section = current_section.get_or_insert_with(Vec::new);
                    current_section.push(JsonPathPiece::ArrayItem(*index));
                }
                MultiJsonPathPiece::ObjectMember(name) => {
                    let current_section = current_section.get_or_insert_with(Vec::new);
                    current_section.push(JsonPathPiece::ObjectMember(name.clone()));
                }
                MultiJsonPathPiece::AllArrayItems { allow_empty } => {
                    if let Some(current_section) = current_section.take() {
                        converted_path.push(PartialPath::JsonPath(current_section));
                    }
                    converted_path.push(PartialPath::AllArrayItems {
                        allow_empty: *allow_empty,
                    });
                }
                MultiJsonPathPiece::OptionalObjectMember(name) => {
                    if let Some(current_section) = current_section.take() {
                        converted_path.push(PartialPath::JsonPath(current_section));
                    }
                    converted_path.push(PartialPath::OptionalObjectMember(name.clone()));
                }
                MultiJsonPathPiece::AllObjectMembers { allow_empty } => {
                    if let Some(current_section) = current_section.take() {
                        converted_path.push(PartialPath::JsonPath(current_section));
                    }
                    converted_path.push(PartialPath::AllObjectMembers {
                        allow_empty: *allow_empty,
                    });
                }
            }
        }

        if let Some(current_section) = current_section {
            converted_path.push(PartialPath::JsonPath(current_section));
        }
        converted_path
    }

    // Get the original location for error reporting
    let original_location = if require_at_least_one_match {
        // Include the JSON path, assuming that users of the Simple API prefer easier troubleshooting over performance
        Some(json_reader.current_position(true))
    } else {
        None
    };

    let path = convert_path(original_path);
    let mut path_index = 0;
    let mut has_match = false;

    // Whether the path is currently traversed downwards, i.e. going to deeper nesting levels
    // If `false` it is either staying at the same level or moving upwards towards top level
    let mut is_moving_down = true;
    loop {
        match &path[path_index] {
            PartialPath::JsonPath(path) => {
                if is_moving_down {
                    json_reader.seek_to(path)?;
                    path_index += 1;
                    // Continue moving down towards end of path
                } else {
                    json_reader.seek_back(path)?;
                    // Continue moving up towards top level
                }
            }
            PartialPath::AllArrayItems { allow_empty } => {
                if is_moving_down {
                    json_reader.begin_array()?;

                    // Check if array is allowed to be empty
                    // Only need to check this for `is_moving_down == true`, because otherwise at least one
                    // array item had already been read
                    if !allow_empty && !json_reader.has_next()? {
                        /*
                         * TODO: Use custom error; relying on `peek()` to trigger error might be too brittle?
                         * Would have to store it in `ErrorSafeJsonReader` then though
                         */
                        return Err(json_reader
                            // Call `peek()` to trigger a `FewerElementsThanExpected` error (since `has_next()` was `false`)
                            .peek()
                            .expect_err("should have failed with `FewerElementsThanExpected`")
                            .into());
                    }
                }

                if json_reader.has_next()? {
                    is_moving_down = true;
                    path_index += 1;
                } else {
                    json_reader.end_array()?;
                    // Move up
                    is_moving_down = false;
                }
            }
            PartialPath::OptionalObjectMember(name) => {
                if is_moving_down {
                    json_reader.begin_object()?;
                    let mut found_member = false;
                    while json_reader.has_next()? {
                        if json_reader.next_name()? == name {
                            found_member = true;
                            path_index += 1;
                            // Continue moving down towards end of path
                            break;
                        } else {
                            json_reader.skip_value()?;
                        }
                    }

                    if !found_member {
                        json_reader.end_object()?;
                        // Move up
                        is_moving_down = false;
                    }
                } else {
                    // Skip remaining members; ignore if there is duplicate member with same name
                    while json_reader.has_next()? {
                        json_reader.skip_name()?;
                        json_reader.skip_value()?;
                    }
                    json_reader.end_object()?;
                    // Continue moving up towards top level
                }
            }
            PartialPath::AllObjectMembers { allow_empty } => {
                if is_moving_down {
                    json_reader.begin_object()?;

                    // Check if object is allowed to be empty
                    // Only need to check this for `is_moving_down == true`, because otherwise at least one
                    // object member had already been read
                    if !allow_empty && !json_reader.has_next()? {
                        /*
                         * TODO: Use custom error; relying on `skip_name()` to trigger error might be too brittle?
                         * Would have to store it in `ErrorSafeJsonReader` then though
                         */
                        return Err(json_reader
                            // Call `skip_name()` to trigger a `FewerElementsThanExpected` error (since `has_next()` was `false`)
                            .skip_name()
                            .expect_err("should have failed with `FewerElementsThanExpected`")
                            .into());
                    }
                }

                if json_reader.has_next()? {
                    json_reader.skip_name()?;
                    is_moving_down = true;
                    path_index += 1;
                } else {
                    json_reader.end_object()?;
                    // Move up
                    is_moving_down = false;
                }
            }
        }

        // Check if the desired value was found
        if is_moving_down && path_index >= path.len() {
            has_match = true;

            read_value(json_reader, &mut f)?;

            match path[path_index - 1] {
                PartialPath::JsonPath(_) | PartialPath::OptionalObjectMember(_) => {}
                // For trailing `AllArrayItems` and `AllObjectMembers` process all their remaining values here;
                // alternatively could also not do anything special here but just let main loop reach the
                // `read_value` call above again, but that might be less efficient
                PartialPath::AllArrayItems { .. } => {
                    // Read all array items
                    while json_reader.has_next()? {
                        read_value(json_reader, &mut f)?;
                    }
                    // Don't call `end_array` yet; main loop will do that at the beginning again
                }
                PartialPath::AllObjectMembers { .. } => {
                    // Read all object members
                    while json_reader.has_next()? {
                        json_reader.skip_name()?;
                        read_value(json_reader, &mut f)?;
                    }
                    // Don't call `end_object` yet; main loop will do that at the beginning again
                }
            }

            // Move up
            is_moving_down = false;
        }

        // Handle moving up towards top level
        if !is_moving_down {
            if path_index == 0 {
                // Finished seeking
                break;
            }
            path_index -= 1;
        }
    }

    if require_at_least_one_match && !has_match {
        // TODO: Should this rather use the notation used by `multi_json_path!` macro?
        let formatted_path = original_path
            .iter()
            .map(|p| match p {
                MultiJsonPathPiece::ArrayItem(index) => format!("[{index}]"),
                MultiJsonPathPiece::AllArrayItems { allow_empty } => {
                    // Note: The `[+]` syntax is not part of the official JSONPath specification
                    if *allow_empty { "[*]" } else { "[+]" }.to_owned()
                }
                MultiJsonPathPiece::ObjectMember(name) => format!(".{name}"),
                // Note: This `.name?` syntax is not part of the official JSONPath specification
                MultiJsonPathPiece::OptionalObjectMember(name) => format!(".{name}?"),
                MultiJsonPathPiece::AllObjectMembers { allow_empty } => {
                    // Note: The `.+` syntax is not part of the official JSONPath specification
                    if *allow_empty { ".*" } else { ".+" }.to_owned()
                }
            })
            .collect::<String>();

        // Report the original location where seeking started because there is no single
        // location where the path had no match, instead the path as a whole had no match
        let original_location = original_location.unwrap();
        if json_reader.error.is_none() {
            // Use dummy error because cannot preserve original error, and because error
            // is specific to `read_seeked_multi` and the provided path, and it would be
            // confusing to repeat it for unrelated subsequent reader calls
            json_reader.error = Some(create_dummy_error(&original_location));
        }
        // TODO Proper error type?
        Err(
            format!("no matching value found for path '{formatted_path}' at {original_location}")
                .into(),
        )
    } else {
        Ok(())
    }
}

mod error_safe_reader {
    use super::*;

    type IoError = std::io::Error;

    pub(super) fn clone_original_io_error(error: &IoError) -> IoError {
        // Report as `Other` kind (and with custom message) to avoid caller indefinitely retrying
        // because it considers the original error kind as safe to retry
        #[allow(clippy::to_string_in_format_args)] // make it explicit that this uses `to_string()`
        IoError::other(format!(
            "previous error '{}': {}",
            error.kind(),
            error.to_string()
        ))
    }

    /// Creates a [`ReaderError`] for situations where the original error cannot be preserved
    pub(super) fn create_dummy_error(location: &JsonReaderPosition) -> ReaderError {
        ReaderError::SyntaxError(JsonSyntaxError {
            // This error kind does not suit that well, but the other kinds suit even worse
            // Mainly have to return 'any' error; users should not rely on this safeguard in the first place
            kind: SyntaxErrorKind::IncompleteDocument,
            location: location.clone(),
        })
    }

    /// Creates a dummy [`ReaderError`] with unknown position
    fn create_unknown_pos_error() -> ReaderError {
        create_dummy_error(&JsonReaderPosition::unknown_position())
    }

    /// If previously an error had occurred, returns that error. Otherwise uses the delegate
    /// reader and in case of an error stores it to prevent subsequent usage.
    /* This is a macro instead of a function for methods returning `&str`, and to support error conversion */
    macro_rules! use_delegate {
        ($self:ident, |$json_reader:ident| $reading_action:expr, |$original_error:ident| $original_error_converter:expr, |$stored_error:ident| $stored_error_converter:expr) => {
            if let Some(error) = &$self.error {
                let $stored_error = error.rough_clone();
                Err($stored_error_converter)
            } else {
                let $json_reader = &mut $self.delegate;
                let result = $reading_action;
                if let Err($original_error) = &result {
                    $self.error = Some($original_error_converter);
                }
                result
            }
        };
        ($self:ident, |$json_reader:ident| $reading_action:expr) => {
            use_delegate!(
                $self,
                |$json_reader| $reading_action,
                |original_error| {
                    match original_error {
                        // Note: List all error types instead of using a 'catch-all' to explicitly decide for each the
                        // correct handling, especially when future error types are being added
                        e @ ReaderError::SyntaxError(_) => e.rough_clone(),
                        e @ ReaderError::MaxNestingDepthExceeded { .. } => e.rough_clone(),
                        e @ ReaderError::UnsupportedNumberValue { .. } => e.rough_clone(),
                        ReaderError::IoError { error, location } => ReaderError::IoError {
                            error: clone_original_io_error(error),
                            location: location.clone(),
                        },
                        // For these repeating the error might be confusing, e.g. when a subsequent call performs a completely unrelated action,
                        // therefore use a dummy error
                        // Technically `JsonReader` allows retrying for these errors, but that would be error-prone when they occurred during a
                        // `seek_to` or similar where the reader position is uncertain afterwards; therefore don't allow retrying
                        ReaderError::UnexpectedValueType { location, .. } => create_dummy_error(location),
                        ReaderError::UnexpectedStructure { location, .. } => create_dummy_error(location),
                    }
                },
                |stored_error| stored_error
            )
        };
    }

    /// [`JsonReader`] implementation which in case of errors keeps returning the error and does
    /// not use the underlying JSON reader anymore
    ///
    /// This is mainly to protect against user-provided closures or functions which accidentally
    /// discard and not propagate reader errors, which could lead to subsequent panics. How exactly
    /// this reader repeats errors or what information it preserves is unspecified; users should
    /// always propagate reader errors and not (intentionally) rely on this safeguard here.
    #[derive(Debug)]
    pub(super) struct ErrorSafeJsonReader<J: JsonReader> {
        pub(super) delegate: J,
        pub(super) error: Option<ReaderError>,
    }

    impl<J: JsonReader> JsonReader for ErrorSafeJsonReader<J> {
        fn peek(&mut self) -> Result<ValueType, ReaderError> {
            use_delegate!(self, |r| r.peek())
        }

        fn begin_object(&mut self) -> Result<(), ReaderError> {
            use_delegate!(self, |r| r.begin_object())
        }

        fn end_object(&mut self) -> Result<(), ReaderError> {
            use_delegate!(self, |r| r.end_object())
        }

        fn begin_array(&mut self) -> Result<(), ReaderError> {
            use_delegate!(self, |r| r.begin_array())
        }

        fn end_array(&mut self) -> Result<(), ReaderError> {
            use_delegate!(self, |r| r.end_array())
        }

        fn has_next(&mut self) -> Result<bool, ReaderError> {
            use_delegate!(self, |r| r.has_next())
        }

        fn next_name(&mut self) -> Result<&str, ReaderError> {
            use_delegate!(self, |r| r.next_name())
        }

        fn next_name_owned(&mut self) -> Result<String, ReaderError> {
            use_delegate!(self, |r| r.next_name_owned())
        }

        fn next_str(&mut self) -> Result<&str, ReaderError> {
            use_delegate!(self, |r| r.next_str())
        }

        fn next_string(&mut self) -> Result<String, ReaderError> {
            use_delegate!(self, |r| r.next_string())
        }

        #[allow(refining_impl_trait)] // this `JsonReader` impl is for an internal struct, so should not cause issues?
        fn next_string_reader(
            &mut self,
        ) -> Result<ErrorSafeStringValueReader<'_, impl Read>, ReaderError> {
            let string_reader_delegate = use_delegate!(self, |r| r.next_string_reader())?;
            Ok(ErrorSafeStringValueReader {
                delegate: string_reader_delegate,
                // Store errors in the `error` field of this `ErrorSafeStringValueReader`, so they are
                // available to the original JsonReader afterwards
                error: &mut self.error,
            })
        }

        fn next_number_as_str(&mut self) -> Result<&str, ReaderError> {
            use_delegate!(self, |r| r.next_number_as_str())
        }

        fn next_number_as_string(&mut self) -> Result<String, ReaderError> {
            use_delegate!(self, |r| r.next_number_as_string())
        }

        fn next_number<T: FromStr>(&mut self) -> Result<Result<T, T::Err>, ReaderError> {
            use_delegate!(self, |r| r.next_number())
        }

        fn next_bool(&mut self) -> Result<bool, ReaderError> {
            use_delegate!(self, |r| r.next_bool())
        }

        fn next_null(&mut self) -> Result<(), ReaderError> {
            use_delegate!(self, |r| r.next_null())
        }

        #[cfg(feature = "serde")]
        fn deserialize_next<'de, D: serde::de::Deserialize<'de>>(
            &mut self,
        ) -> Result<D, crate::serde::DeserializerError> {
            use crate::serde::DeserializerError;

            use_delegate!(
                self,
                |r| r.deserialize_next(),
                |original_error| {
                    match original_error {
                        DeserializerError::ReaderError(e) => e.rough_clone(),
                        // Cannot easily preserve information for these errors
                        DeserializerError::Custom(_) => create_unknown_pos_error(),
                        DeserializerError::MaxNestingDepthExceeded(_) => create_unknown_pos_error(),
                        DeserializerError::InvalidNumber(_) => create_unknown_pos_error(),
                    }
                },
                |stored_error| DeserializerError::ReaderError(stored_error)
            )
        }

        fn skip_name(&mut self) -> Result<(), ReaderError> {
            use_delegate!(self, |r| r.skip_name())
        }

        fn skip_value(&mut self) -> Result<(), ReaderError> {
            use_delegate!(self, |r| r.skip_value())
        }

        fn skip_to_top_level(&mut self) -> Result<(), ReaderError> {
            use_delegate!(self, |r| r.skip_to_top_level())
        }

        fn transfer_to<W: JsonWriter>(&mut self, json_writer: &mut W) -> Result<(), TransferError> {
            use_delegate!(
                self,
                |r| r.transfer_to(json_writer),
                |original_error| match original_error {
                    TransferError::ReaderError(e) => e.rough_clone(),
                    // Cannot easily preserve this, and reporting it as reader IO error might be confusing
                    TransferError::WriterError(_) => create_unknown_pos_error(),
                },
                |stored_error| TransferError::ReaderError(stored_error)
            )
        }

        fn current_position(&self, include_path: bool) -> JsonReaderPosition {
            // Permit calling this even if error occurred before
            self.delegate.current_position(include_path)
        }

        fn seek_to(&mut self, rel_json_path: &JsonPath) -> Result<(), ReaderError> {
            use_delegate!(self, |r| r.seek_to(rel_json_path))
        }

        fn seek_back(&mut self, rel_json_path: &JsonPath) -> Result<(), ReaderError> {
            use_delegate!(self, |r| r.seek_back(rel_json_path))
        }

        fn consume_trailing_whitespace(self) -> Result<(), ReaderError> {
            // Special code instead of `use_delegate!(...)` because this method consumes `self`
            if let Some(error) = self.error {
                return Err(error);
            }
            self.delegate.consume_trailing_whitespace()
        }
    }

    // Note: Repeating errors here might be a bit redundant if JsonStreamReader is used since it does
    // this itself as well; but that is not guaranteed for all JsonReader implementations
    pub(super) struct ErrorSafeStringValueReader<'a, D: Read> {
        delegate: D,
        pub(super) error: &'a mut Option<ReaderError>,
    }
    impl<D: Read> ErrorSafeStringValueReader<'_, D> {
        fn use_delegate<T>(
            &mut self,
            f: impl FnOnce(&mut D) -> std::io::Result<T>,
        ) -> std::io::Result<T> {
            if let Some(error) = &self.error {
                return Err(match error.rough_clone() {
                    // Ignore `location`; assuming that IO error was set here by ErrorSafeStringValueReader
                    // and therefore no real location exists (or original location would already be included
                    // in error message)
                    ReaderError::IoError { error, .. } => error,
                    // Error should have only been set by ErrorSafeStringValueReader, and therefore be IoError;
                    // any previous other error type should have prevented creation of ErrorSafeStringValueReader
                    e => unreachable!("unexpected error type: {e:?}"),
                });
            }

            let result = f(&mut self.delegate);
            if let Err(error) = &result {
                *self.error = Some(ReaderError::IoError {
                    error: clone_original_io_error(error),
                    location: JsonReaderPosition::unknown_position(),
                });
            }
            result
        }
    }
    impl<D: Read> Read for ErrorSafeStringValueReader<'_, D> {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            self.use_delegate(|d| d.read(buf))
        }
    }
}

/// JSON reader variant which is easier to use than [`JsonReader`]
///
/// This JSON reader variant ensures correct usage at compile-time making it easier and less
/// error-prone to use than [`JsonReader`], which validates correct usage at runtime and panics
/// on incorrect usage. However, this comes at the cost of `SimpleJsonReader` being less flexible
/// to use, and it not offering all features of [`JsonReader`].
///
/// When an error is returned by one of the methods of the reader, the error should be propagated
/// (for example by using Rust's `?` operator), processing should be aborted and the reader should
/// not be used any further.
///
/// # Examples
/// ```
/// # use struson::reader::simple::*;
/// // In this example JSON data comes from a string;
/// // normally it would come from a file or a network connection
/// let json_reader = SimpleJsonReader::new(r#"["a", "short", "example"]"#.as_bytes());
/// let mut words = Vec::<String>::new();
/// json_reader.read_array_items(|item_reader| {
///     let word = item_reader.read_string()?;
///     words.push(word);
///     Ok(())
/// })?;
/// assert_eq!(words, vec!["a", "short", "example"]);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Debug)]
pub struct SimpleJsonReader<J: JsonReader> {
    json_reader: ErrorSafeJsonReader<J>,
    /// Whether [`seek_to`] has been used
    has_seeked: bool,
}
impl<J: JsonReader> SimpleJsonReader<J> {
    /// Creates a new `SimpleJsonReader` from the given [`JsonReader`]
    ///
    /// The `JsonReader` acts as delegate which performs the actual JSON reading. It should
    /// be positioned at the start of the top-level JSON value and should not have consumed
    /// any data yet, otherwise the behavior of the created `SimpleJsonReader` is unspecified
    /// and it may panic.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::*;
    /// # use struson::reader::simple::*;
    /// let json = r"
    ///     [
    ///         1,
    ///         2,
    ///     ]
    ///     ".as_bytes();
    ///
    /// # #[allow(unused_variables)]
    /// let json_reader = SimpleJsonReader::from_json_reader(
    ///     JsonStreamReader::new_custom(
    ///         json,
    ///         ReaderSettings {
    ///             allow_trailing_comma: true,
    ///             // For all other settings use the default
    ///             ..Default::default()
    ///         },
    ///     )
    /// );
    /// ```
    pub fn from_json_reader(json_reader: J) -> Self {
        SimpleJsonReader {
            json_reader: ErrorSafeJsonReader {
                delegate: json_reader,
                error: None,
            },
            has_seeked: false,
        }
    }

    /// Seeks to the specified location in the JSON document
    ///
    /// Seeks to the specified relative JSON path in the JSON document by skipping all previous
    /// values. Once this method returns successfully the reader will be positioned before the
    /// last element specified by the path.
    ///
    /// For example for the JSON path `json_path!["foo", 2]` it will start consuming a JSON object,
    /// skipping members until it finds one with name "foo". Then it starts consuming the member
    /// value, expecting that it is a JSON array, until right before the array item with (starting
    /// at 0) index 2. If multiple members in a JSON object have the same name (for example
    /// `{"a": 1, "a": 2}`) this method will seek to the first occurrence.
    ///
    /// Seeking to a specific location can be useful when parts of the processed JSON document
    /// are not relevant for the application processing it.
    ///
    /// If the structure of the JSON data does not match the path, for example when the JSON data
    /// contains an array but the path expects an object, an error is returned.
    ///
    /// The seeking behavior of this method is equivalent to [`read_seeked`](Self::read_seeked), but
    /// `seek_to` allows consuming the value afterwards without having to use a closure or separate
    /// function (as required by `read_seeked`), however it is only available for `SimpleJsonReader`
    /// and not generally for the `ValueReader` trait.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// # use struson::reader::json_path::*;
    /// let mut json_reader = SimpleJsonReader::new(
    ///     r#"{"bar": true, "foo": ["a", "b", "c"]}"#.as_bytes()
    /// );
    /// json_reader.seek_to(&json_path!["foo", 2])?;
    ///
    /// // Can now consume the value to which the call seeked to
    /// let value = json_reader.read_string()?;
    /// assert_eq!(value, "c");
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    /*
     * Only provided for top-level reader but not for nested arrays or objects, because they implicitly
     * close the open arrays and objects, which would panic because `seek_to` opens additional arrays
     * and objects. Maybe most of the `ValueReader` implementations here could track that and let the
     * caller close the arrays and objects, but for `ArrayReader` it would cause problems because seeking
     * would break its `has_next` method, which expects to always be inside the original array.
     */
    pub fn seek_to(&mut self, path: &JsonPath) -> Result<(), ReaderError> {
        self.has_seeked = true;
        self.json_reader.seek_to(path)
    }

    fn finish(mut self) -> Result<(), ReaderError> {
        // TODO: Or should for `has_seeked` simply stop processing without any skipping and without
        //       call to `consume_trailing_whitespace`?
        if self.has_seeked {
            self.json_reader.skip_to_top_level()?;
        }
        self.json_reader.consume_trailing_whitespace()
    }
}
impl<R: Read> SimpleJsonReader<JsonStreamReader<R>> {
    /// Creates a new JSON reader
    ///
    /// The given reader must provide the JSON data UTF-8 encoded, without leading byte order mark (BOM).
    /// Internally this creates a [`JsonStreamReader`] which acts as delegate; see its documentation for
    /// more information about the parsing behavior and security considerations.
    pub fn new(reader: R) -> Self {
        SimpleJsonReader::from_json_reader(JsonStreamReader::new(reader))
    }
}

// These methods all call `json_reader.consume_trailing_whitespace()` because `SimpleJsonReader`
// is intended to be used for top-level value
impl<J: JsonReader> ValueReader<J> for SimpleJsonReader<J> {
    fn peek_value(&mut self) -> Result<ValueType, ReaderError> {
        self.json_reader.peek()
    }

    fn read_null(mut self) -> Result<(), ReaderError> {
        self.json_reader.next_null()?;
        self.finish()
    }

    fn read_bool(mut self) -> Result<bool, ReaderError> {
        let result = self.json_reader.next_bool()?;
        self.finish()?;
        Ok(result)
    }

    fn read_str<T>(
        mut self,
        f: impl FnOnce(&str) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        let result = f(self.json_reader.next_str()?)?;
        self.finish()?;
        Ok(result)
    }

    fn read_string(mut self) -> Result<String, ReaderError> {
        let result = self.json_reader.next_string()?;
        self.finish()?;
        Ok(result)
    }

    fn read_string_with_reader<T>(
        mut self,
        f: impl FnOnce(StringValueReader<'_>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        let result = read_string_with_reader(&mut self.json_reader, f)?;
        self.finish()?;
        Ok(result)
    }

    fn read_number<T: FromStr>(mut self) -> Result<Result<T, T::Err>, ReaderError> {
        let result = self.json_reader.next_number()?;
        self.finish()?;
        Ok(result)
    }

    fn read_number_as_string(mut self) -> Result<String, ReaderError> {
        let result = self.json_reader.next_number_as_string()?;
        self.finish()?;
        Ok(result)
    }

    #[cfg(feature = "serde")]
    fn read_deserialize<'de, D: serde::de::Deserialize<'de>>(
        mut self,
    ) -> Result<D, crate::serde::DeserializerError> {
        let result = self.json_reader.deserialize_next()?;
        self.finish()?;
        Ok(result)
    }

    fn skip_value(mut self) -> Result<(), ReaderError> {
        self.json_reader.skip_value()?;
        self.finish()
    }

    fn read_array<T>(
        mut self,
        f: impl FnOnce(&mut ArrayReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        let result = read_array(&mut self.json_reader, f)?;
        self.finish()?;
        Ok(result)
    }

    fn read_object_borrowed_names(
        mut self,
        f: impl FnMut(MemberReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        read_object_borrowed_names(&mut self.json_reader, f)?;
        self.finish()?;
        Ok(())
    }

    fn read_object_owned_names(
        mut self,
        f: impl FnMut(String, SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        read_object_owned_names(&mut self.json_reader, f)?;
        self.finish()?;
        Ok(())
    }

    fn read_seeked<T>(
        mut self,
        path: &JsonPath,
        f: impl FnOnce(SingleValueReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        let result = read_seeked(&mut self.json_reader, path, f)?;
        self.finish()?;
        Ok(result)
    }

    fn read_seeked_multi(
        mut self,
        path: &MultiJsonPath,
        at_least_one_match: bool,
        f: impl FnMut(SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        read_seeked_multi(&mut self.json_reader, path, at_least_one_match, f)?;
        self.finish()?;
        Ok(())
    }
}

/// Reader for an arbitrary amount of JSON array items
///
/// This struct is used by [`ValueReader::read_array`].
#[derive(Debug)]
pub struct ArrayReader<'a, J: JsonReader> {
    json_reader: &'a mut ErrorSafeJsonReader<J>,
}
impl<J: JsonReader> ArrayReader<'_, J> {
    /// Checks if there is a next item in the JSON array, without consuming it
    ///
    /// Returns `true` if there is a next item, `false` otherwise. This method can be
    /// useful as condition of a `while` loop when processing a JSON array of unknown size.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// let json_reader = SimpleJsonReader::new("[1, 2]".as_bytes());
    /// json_reader.read_array(|array_reader| {
    ///     while array_reader.has_next()? {
    ///         let value = array_reader.read_number_as_string()?;
    ///         println!("{value}");
    ///     }
    /// #   assert!(!array_reader.has_next()?);
    ///     Ok(())
    /// })?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn has_next(&mut self) -> Result<bool, ReaderError> {
        self.json_reader.has_next()
    }
}

// Implement for `&mut ArrayReader` to allow reading multiple values instead of just one
impl<J: JsonReader> ValueReader<J> for &mut ArrayReader<'_, J> {
    fn peek_value(&mut self) -> Result<ValueType, ReaderError> {
        self.json_reader.peek()
    }

    fn read_null(self) -> Result<(), ReaderError> {
        self.json_reader.next_null()
    }

    fn read_bool(self) -> Result<bool, ReaderError> {
        self.json_reader.next_bool()
    }

    fn read_str<T>(
        self,
        f: impl FnOnce(&str) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        f(self.json_reader.next_str()?)
    }

    fn read_string(self) -> Result<String, ReaderError> {
        self.json_reader.next_string()
    }

    fn read_string_with_reader<T>(
        self,
        f: impl FnOnce(StringValueReader<'_>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        read_string_with_reader(self.json_reader, f)
    }

    fn read_number<T: FromStr>(self) -> Result<Result<T, T::Err>, ReaderError> {
        self.json_reader.next_number()
    }

    fn read_number_as_string(self) -> Result<String, ReaderError> {
        self.json_reader.next_number_as_string()
    }

    #[cfg(feature = "serde")]
    fn read_deserialize<'de, D: serde::de::Deserialize<'de>>(
        self,
    ) -> Result<D, crate::serde::DeserializerError> {
        self.json_reader.deserialize_next()
    }

    fn skip_value(self) -> Result<(), ReaderError> {
        self.json_reader.skip_value()
    }

    fn read_array<T>(
        self,
        f: impl FnOnce(&mut ArrayReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        read_array(self.json_reader, f)
    }

    fn read_object_borrowed_names(
        self,
        f: impl FnMut(MemberReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        read_object_borrowed_names(self.json_reader, f)
    }

    fn read_object_owned_names(
        self,
        f: impl FnMut(String, SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        read_object_owned_names(self.json_reader, f)
    }

    fn read_seeked<T>(
        self,
        path: &JsonPath,
        f: impl FnOnce(SingleValueReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        read_seeked(self.json_reader, path, f)
    }

    fn read_seeked_multi(
        self,
        path: &MultiJsonPath,
        at_least_one_match: bool,
        f: impl FnMut(SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        read_seeked_multi(self.json_reader, path, at_least_one_match, f)
    }
}

/// Reader for a single JSON value
///
/// This struct is used by
/// - [`ValueReader::read_array_items`]
/// - [`ValueReader::read_object_owned_names`]
/// - [`ValueReader::read_seeked_multi`]
#[derive(Debug)]
pub struct SingleValueReader<'a, J: JsonReader> {
    json_reader: &'a mut ErrorSafeJsonReader<J>,
    consumed_value: &'a mut bool,
}
impl<J: JsonReader> ValueReader<J> for SingleValueReader<'_, J> {
    fn peek_value(&mut self) -> Result<ValueType, ReaderError> {
        self.json_reader.peek()
    }

    fn read_null(self) -> Result<(), ReaderError> {
        *self.consumed_value = true;
        self.json_reader.next_null()
    }

    fn read_bool(self) -> Result<bool, ReaderError> {
        *self.consumed_value = true;
        self.json_reader.next_bool()
    }

    fn read_str<T>(
        self,
        f: impl FnOnce(&str) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        *self.consumed_value = true;
        f(self.json_reader.next_str()?)
    }

    fn read_string(self) -> Result<String, ReaderError> {
        *self.consumed_value = true;
        self.json_reader.next_string()
    }

    fn read_string_with_reader<T>(
        self,
        f: impl FnOnce(StringValueReader<'_>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        *self.consumed_value = true;
        read_string_with_reader(self.json_reader, f)
    }

    fn read_number<T: FromStr>(self) -> Result<Result<T, T::Err>, ReaderError> {
        *self.consumed_value = true;
        self.json_reader.next_number()
    }

    fn read_number_as_string(self) -> Result<String, ReaderError> {
        *self.consumed_value = true;
        self.json_reader.next_number_as_string()
    }

    #[cfg(feature = "serde")]
    fn read_deserialize<'de, D: serde::de::Deserialize<'de>>(
        self,
    ) -> Result<D, crate::serde::DeserializerError> {
        *self.consumed_value = true;
        self.json_reader.deserialize_next()
    }

    fn skip_value(self) -> Result<(), ReaderError> {
        *self.consumed_value = true;
        self.json_reader.skip_value()
    }

    fn read_array<T>(
        self,
        f: impl FnOnce(&mut ArrayReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        *self.consumed_value = true;
        read_array(self.json_reader, f)
    }

    fn read_object_borrowed_names(
        self,
        f: impl FnMut(MemberReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        *self.consumed_value = true;
        read_object_borrowed_names(self.json_reader, f)
    }

    fn read_object_owned_names(
        self,
        f: impl FnMut(String, SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        *self.consumed_value = true;
        read_object_owned_names(self.json_reader, f)
    }

    fn read_seeked<T>(
        self,
        path: &JsonPath,
        f: impl FnOnce(SingleValueReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        *self.consumed_value = true;
        read_seeked(self.json_reader, path, f)
    }

    fn read_seeked_multi(
        self,
        path: &MultiJsonPath,
        at_least_one_match: bool,
        f: impl FnMut(SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        *self.consumed_value = true;
        read_seeked_multi(self.json_reader, path, at_least_one_match, f)
    }
}

/// Reader for a JSON object member
///
/// The member name can be read using [`read_name`](Self::read_name), and afterwards
/// the member value can be read using one of the [`ValueReader`] methods.
///
/// This struct is used by [`ValueReader::read_object_borrowed_names`].
#[derive(Debug)]
pub struct MemberReader<'a, J: JsonReader> {
    json_reader: &'a mut ErrorSafeJsonReader<J>,
    consumed_name: &'a mut bool,
    consumed_value: &'a mut bool,
}
impl<J: JsonReader> MemberReader<'_, J> {
    /// Reads the member name
    ///
    /// Panics if called more than once.
    pub fn read_name(&mut self) -> Result<&str, ReaderError> {
        /*
         * Ideally this would not panic but instead keep returning the same reference on
         * subsequent calls
         * In theory this should be safe to implement by storing the reference after the first
         * read in the struct, and due to borrowing rules the member value cannot be consumed
         * while the name from `read_name` is still referenced. Also when the member value is
         * read, `self` is consumed so the name cannot be accessed afterwards anymore.
         *
         * However, the Rust compiler does not seem to permit this, see also https://stackoverflow.com/q/32300132.
         * So for now panic, which should be fine assuming that normally users don't call
         * `read_name` multiple times.
         * But also the method name `read_name` suggests that it advances the reader, so it
         * might be counterintuitive that subsequent calls return a previously read name.
         */
        if *self.consumed_name {
            panic!("name has already been consumed");
        }
        *self.consumed_name = true;
        self.json_reader.next_name()
    }

    fn check_skip_name(&mut self) -> Result<(), ReaderError> {
        if !*self.consumed_name {
            *self.consumed_name = true;
            self.json_reader.skip_name()?;
        }
        Ok(())
    }
}

/// The `ValueReader` methods read the member value
impl<J: JsonReader> ValueReader<J> for MemberReader<'_, J> {
    /// Peeks at the type of the member value, without consuming it
    ///
    /// If [`read_name`](MemberReader::read_name) has not been called yet, the
    /// member name will be skipped implicitly and calling `read_name` will not
    /// be possible anymore afterwards.
    fn peek_value(&mut self) -> Result<ValueType, ReaderError> {
        self.check_skip_name()?;
        self.json_reader.peek()
    }

    fn read_null(mut self) -> Result<(), ReaderError> {
        self.check_skip_name()?;
        *self.consumed_value = true;
        self.json_reader.next_null()
    }

    fn read_bool(mut self) -> Result<bool, ReaderError> {
        self.check_skip_name()?;
        *self.consumed_value = true;
        self.json_reader.next_bool()
    }

    fn read_str<T>(
        mut self,
        f: impl FnOnce(&str) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        self.check_skip_name()?;
        *self.consumed_value = true;
        f(self.json_reader.next_str()?)
    }

    fn read_string(mut self) -> Result<String, ReaderError> {
        self.check_skip_name()?;
        *self.consumed_value = true;
        self.json_reader.next_string()
    }

    fn read_string_with_reader<T>(
        mut self,
        f: impl FnOnce(StringValueReader<'_>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        self.check_skip_name()?;
        *self.consumed_value = true;
        read_string_with_reader(self.json_reader, f)
    }

    fn read_number<T: FromStr>(mut self) -> Result<Result<T, T::Err>, ReaderError> {
        self.check_skip_name()?;
        *self.consumed_value = true;
        self.json_reader.next_number()
    }

    fn read_number_as_string(mut self) -> Result<String, ReaderError> {
        self.check_skip_name()?;
        *self.consumed_value = true;
        self.json_reader.next_number_as_string()
    }

    #[cfg(feature = "serde")]
    fn read_deserialize<'de, D: serde::de::Deserialize<'de>>(
        mut self,
    ) -> Result<D, crate::serde::DeserializerError> {
        self.check_skip_name()?;
        *self.consumed_value = true;
        self.json_reader.deserialize_next()
    }

    fn skip_value(mut self) -> Result<(), ReaderError> {
        self.check_skip_name()?;
        *self.consumed_value = true;
        self.json_reader.skip_value()
    }

    fn read_array<T>(
        mut self,
        f: impl FnOnce(&mut ArrayReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        self.check_skip_name()?;
        *self.consumed_value = true;
        read_array(self.json_reader, f)
    }

    fn read_object_borrowed_names(
        mut self,
        f: impl FnMut(MemberReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        self.check_skip_name()?;
        *self.consumed_value = true;
        read_object_borrowed_names(self.json_reader, f)
    }

    fn read_object_owned_names(
        mut self,
        f: impl FnMut(String, SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        self.check_skip_name()?;
        *self.consumed_value = true;
        read_object_owned_names(self.json_reader, f)
    }

    fn read_seeked<T>(
        mut self,
        path: &JsonPath,
        f: impl FnOnce(SingleValueReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        self.check_skip_name()?;
        *self.consumed_value = true;
        read_seeked(self.json_reader, path, f)
    }

    fn read_seeked_multi(
        mut self,
        path: &MultiJsonPath,
        at_least_one_match: bool,
        f: impl FnMut(SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        self.check_skip_name()?;
        *self.consumed_value = true;
        read_seeked_multi(self.json_reader, path, at_least_one_match, f)
    }
}

/// Reader for a JSON string value
///
/// This struct is used by [`ValueReader::read_string_with_reader`].
///
/// # Errors
/// A [`std::io::Error`] is returned when the underlying reader encounters an error, or
/// when malformed JSON data is encountered.
///
/// # Error behavior
/// The error behavior of this string reader differs from the guarantees made by [`Read`]:
/// - if an error is returned there are no guarantees about if or how many data has been
///   consumed from the underlying data source and been stored in the provided `buf`
/// - if an error occurs, processing should be aborted, regardless of the kind of the error;
///   trying to use this string reader or the original JSON reader afterwards will lead
///   to unspecified behavior
/* TODO: Should implement `Debug`, but seems to not be easily possible when using `dyn` below */
pub struct StringValueReader<'a> {
    // TODO: Ideally would avoid `dyn` here, but using generic type parameter seems to not be
    //   easily possible when `JsonReader::next_string_reader()` does not use associated type
    //   and `FnOnce` cannot use `impl Trait` for arguments
    delegate: &'a mut dyn Read,
}
impl Read for StringValueReader<'_> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.delegate.read(buf)
    }
}
