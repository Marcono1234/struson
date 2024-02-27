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

use std::{cell::Cell, error::Error, io::Read, rc::Rc, str::FromStr};

use self::multi_json_path::MultiJsonPath;
use crate::reader::{
    json_path::{JsonPath, JsonPathPiece},
    simple::multi_json_path::MultiJsonPathPiece,
    JsonReader, JsonStreamReader, ReaderError, ValueType,
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
    /// | number of type `u32` | [`MultiJsonPathPiece::ArrayItem`] |
    /// | string | [`MultiJsonPathPiece::ObjectMember`] |
    /// | '`?`_string_' | [`MultiJsonPathPiece::OptionalObjectMember`] |
    /// | '`[*]`' | [`MultiJsonPathPiece::AllArrayItems { allow_empty: true }`](MultiJsonPathPiece::AllArrayItems) |
    /// | '`[+]`' | [`MultiJsonPathPiece::AllArrayItems { allow_empty: false }`](MultiJsonPathPiece::AllArrayItems) |
    /// | '`{*}`' | [`MultiJsonPathPiece::AllObjectMembers { allow_empty: true }`](MultiJsonPathPiece::AllObjectMembers) |
    /// | '`{+}`' | [`MultiJsonPathPiece::AllObjectMembers { allow_empty: false }`](MultiJsonPathPiece::AllObjectMembers) |
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
    /// Then the following multi JSON path could be used to match all awards any book has
    /// received:
    /// ```
    /// # use struson::reader::simple::multi_json_path::*;
    /// let json_path = multi_json_path![
    ///     "books",
    ///     [*], // match all books
    ///     ?"awards", // match the optional "awards" member
    ///     [+], // match all awards
    /// ];
    ///
    /// assert_eq!(
    ///     json_path,
    ///     [
    ///         MultiJsonPathPiece::ObjectMember("books".to_owned()),
    ///         MultiJsonPathPiece::AllArrayItems { allow_empty: true },
    ///         MultiJsonPathPiece::OptionalObjectMember("awards".to_owned()),
    ///         MultiJsonPathPiece::AllArrayItems { allow_empty: false },
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

    /// Consumes and returns a JSON string value
    fn read_string(self) -> Result<String, ReaderError>;

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
                let consumed_item = Rc::new(Cell::new(false));
                let item_reader = SingleValueReader {
                    json_reader: array_reader.json_reader,
                    consumed_value: Rc::clone(&consumed_item),
                };
                f(item_reader)?;
                // If the function did not consume the item, skip it
                if !consumed_item.get() {
                    array_reader.json_reader.skip_value()?;
                }
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
    /// println!("a = {a:?}");
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

    /// Seeks to multiple values and consumes them
    ///
    /// Based on the given `path` this method seeks to all matching values, if any, and calls the
    /// function `f` repeatedly for reading each value. If the function returns `Ok` but did not
    /// consume the value, it will be skipped automatically.
    ///
    /// Depending on what pieces the path consists of, it can match any number of values, including
    /// none. The `at_least_one_match` argument determines the behavior of this method in case the
    /// path can potentially match no values. If `true` an error is returned, if `false` no error is
    /// returned but `f` is also not called. `at_least_one_match` can for example be useful when a
    /// [JSON object member is optional](MultiJsonPathPiece::OptionalObjectMember) but for multiple
    /// of such objects at least one is expected to have the member.\
    /// `at_least_one_match = false` does not override the behavior for path pieces which themself
    /// require at least one match, such as [`MultiJsonPathPiece::AllArrayItems { allow_empty: false }`](MultiJsonPathPiece::AllArrayItems).
    ///
    /// For [`MultiJsonPathPiece::ObjectMember`] and [`MultiJsonPathPiece::OptionalObjectMember`]
    /// if multiple members in a JSON object have the same name (for example `{"a": 1, "a": 2}`)
    /// this method will only seek to the first occurrence in that object ignoring the others.
    ///
    /// If the structure of the JSON data does not match the path, for example the JSON data contains
    /// an array but the path expects an object, an error is returned.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// # use struson::reader::simple::multi_json_path::*;
    /// let json = r#"
    /// {
    ///     "books": [
    ///         {
    ///             "title": "A normal day in the life of an ant",
    ///             "awards": [
    ///                 "Best Thriller",
    ///                 "Best Short Story"
    ///             ]
    ///         },
    ///         {
    ///             "name": "Tired of Potatoes",
    ///             "awards": [
    ///                 "Best Drama"
    ///             ]
    ///         }
    ///     ]
    /// }
    /// "#;
    /// let json_reader = SimpleJsonReader::new(json.as_bytes());
    ///
    /// let mut all_awards = Vec::<String>::new();
    /// // Select the awards of all books
    /// let json_path = multi_json_path!["books", [*], "awards", [*]];
    /// json_reader.read_seeked_multi(&json_path, false, |value_reader| {
    ///     let award = value_reader.read_string()?;
    ///     all_awards.push(award);
    ///     Ok(())
    /// })?;
    ///
    /// assert_eq!(
    ///     all_awards,
    ///     vec!["Best Thriller", "Best Short Story", "Best Drama"]
    /// );
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
    json_reader: &mut J,
    f: impl FnOnce(&mut ArrayReader<'_, J>) -> Result<T, Box<dyn Error>>,
) -> Result<T, Box<dyn Error>> {
    json_reader.begin_array()?;
    let mut array_reader = ArrayReader { json_reader };
    let result = f(&mut array_reader)?;
    json_reader.end_array()?;
    Ok(result)
}

fn read_object_borrowed_names<J: JsonReader>(
    json_reader: &mut J,
    mut f: impl FnMut(MemberReader<'_, J>) -> Result<(), Box<dyn Error>>,
) -> Result<(), Box<dyn Error>> {
    json_reader.begin_object()?;
    while json_reader.has_next()? {
        let consumed_name = Rc::new(Cell::new(false));
        let consumed_value = Rc::new(Cell::new(false));
        let member_reader = MemberReader {
            json_reader,
            consumed_name: Rc::clone(&consumed_name),
            consumed_value: Rc::clone(&consumed_value),
        };
        f(member_reader)?;
        // If the function did not consume the member name or value, skip them
        if !consumed_name.get() {
            json_reader.skip_name()?;
        }
        if !consumed_value.get() {
            json_reader.skip_value()?;
        }
    }
    json_reader.end_object()?;
    Ok(())
}

fn read_object_owned_names<J: JsonReader>(
    json_reader: &mut J,
    mut f: impl FnMut(String, SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
) -> Result<(), Box<dyn Error>> {
    json_reader.begin_object()?;
    while json_reader.has_next()? {
        let name = json_reader.next_name_owned()?;
        let consumed_value = Rc::new(Cell::new(false));
        let member_value_reader = SingleValueReader {
            json_reader,
            consumed_value: Rc::clone(&consumed_value),
        };
        f(name, member_value_reader)?;
        // If the function did not consume the value, skip it
        if !consumed_value.get() {
            json_reader.skip_value()?;
        }
    }
    json_reader.end_object()?;
    Ok(())
}

fn read_seeked_multi<J: JsonReader>(
    json_reader: &mut J,
    original_path: &MultiJsonPath,
    require_at_least_one_match: bool,
    mut f: impl FnMut(SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
) -> Result<(), Box<dyn Error>> {
    /// Reads a value with `f`, implicitly skipping the value if `f` did not consume it
    fn read_value<J: JsonReader>(
        json_reader: &mut J,
        f: &mut impl FnMut(SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        let consumed_value = Rc::new(Cell::new(false));
        let value_reader = SingleValueReader {
            json_reader,
            consumed_value: Rc::clone(&consumed_value),
        };

        f(value_reader)?;
        // If the function did not consume the value, skip it
        if !consumed_value.get() {
            json_reader.skip_value()?;
        }
        Ok(())
    }

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

    /// 'Undoes' a `seek_to` call by consuming remaining array items and
    /// object members and closing arrays and objects in reverse order
    fn undo_seek<J: JsonReader>(json_reader: &mut J, path: &JsonPath) -> Result<(), ReaderError> {
        // Undo seek piece by piece in reverse order
        for piece in path.iter().rev() {
            match piece {
                JsonPathPiece::ArrayItem(_) => {
                    // Skip remaining items
                    while json_reader.has_next()? {
                        json_reader.skip_value()?;
                    }
                    json_reader.end_array()?;
                }
                JsonPathPiece::ObjectMember(_) => {
                    // Skip remaining members
                    while json_reader.has_next()? {
                        json_reader.skip_name()?;
                        json_reader.skip_value()?;
                    }
                    json_reader.end_object()?;
                }
            }
        }
        Ok(())
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
                    undo_seek(json_reader, path)?;
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
                        // Note: Location points at closing ']'
                        let location = json_reader.current_position(true);
                        // TODO Proper error type? Or use `ReaderError::UnexpectedStructure` with `FewerElementsThanExpected`?
                        return Err(format!("unexpected empty array at {location}").into());
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
                        // Note: Location points at closing '}'
                        let location = json_reader.current_position(true);
                        // TODO Proper error type? Or use `ReaderError::UnexpectedStructure` with `FewerElementsThanExpected`?
                        return Err(format!("unexpected empty object at {location}").into());
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
        // TODO Proper error type?
        Err(
            format!("no matching value found for path '{formatted_path}' at {original_location}")
                .into(),
        )
    } else {
        Ok(())
    }
}

/// JSON reader variant which is easier to use than [`JsonReader`]
///
/// This JSON reader variant ensures correct usage at compile-time making it easier and less
/// error-prone to use than [`JsonReader`], which validates correct usage at runtime and panics
/// on incorrect usage. However, this comes at the cost of `SimpleJsonReader` being less flexible
/// to use, and it not offerring all features of [`JsonReader`].
///
/// When an error is returned by one of the methods of the reader, processing should be aborted
/// and the reader should not be used any further.
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
    json_reader: J,
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
            json_reader,
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
    pub fn seek_to(&mut self, rel_json_path: &JsonPath) -> Result<(), ReaderError> {
        self.has_seeked = true;
        self.json_reader.seek_to(rel_json_path)
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

    fn read_string(mut self) -> Result<String, ReaderError> {
        let result = self.json_reader.next_string()?;
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
    json_reader: &'a mut J,
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

    fn read_string(self) -> Result<String, ReaderError> {
        self.json_reader.next_string()
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
    json_reader: &'a mut J,
    consumed_value: Rc<Cell<bool>>,
}
impl<J: JsonReader> ValueReader<J> for SingleValueReader<'_, J> {
    fn peek_value(&mut self) -> Result<ValueType, ReaderError> {
        self.json_reader.peek()
    }

    fn read_null(self) -> Result<(), ReaderError> {
        self.consumed_value.set(true);
        self.json_reader.next_null()
    }

    fn read_bool(self) -> Result<bool, ReaderError> {
        self.consumed_value.set(true);
        self.json_reader.next_bool()
    }

    fn read_string(self) -> Result<String, ReaderError> {
        self.consumed_value.set(true);
        self.json_reader.next_string()
    }

    fn read_number<T: FromStr>(self) -> Result<Result<T, T::Err>, ReaderError> {
        self.consumed_value.set(true);
        self.json_reader.next_number()
    }

    fn read_number_as_string(self) -> Result<String, ReaderError> {
        self.consumed_value.set(true);
        self.json_reader.next_number_as_string()
    }

    #[cfg(feature = "serde")]
    fn read_deserialize<'de, D: serde::de::Deserialize<'de>>(
        self,
    ) -> Result<D, crate::serde::DeserializerError> {
        self.consumed_value.set(true);
        self.json_reader.deserialize_next()
    }

    fn skip_value(self) -> Result<(), ReaderError> {
        self.consumed_value.set(true);
        self.json_reader.skip_value()
    }

    fn read_array<T>(
        self,
        f: impl FnOnce(&mut ArrayReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        self.consumed_value.set(true);
        read_array(self.json_reader, f)
    }

    fn read_object_borrowed_names(
        self,
        f: impl FnMut(MemberReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        self.consumed_value.set(true);
        read_object_borrowed_names(self.json_reader, f)
    }

    fn read_object_owned_names(
        self,
        f: impl FnMut(String, SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        self.consumed_value.set(true);
        read_object_owned_names(self.json_reader, f)
    }

    fn read_seeked_multi(
        self,
        path: &MultiJsonPath,
        at_least_one_match: bool,
        f: impl FnMut(SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        self.consumed_value.set(true);
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
    json_reader: &'a mut J,
    consumed_name: Rc<Cell<bool>>,
    consumed_value: Rc<Cell<bool>>,
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
        if self.consumed_name.get() {
            panic!("name has already been consumed");
        }
        self.consumed_name.set(true);
        self.json_reader.next_name()
    }

    fn check_skip_name(&mut self) -> Result<(), ReaderError> {
        if !self.consumed_name.get() {
            self.consumed_name.set(true);
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
        self.consumed_value.set(true);
        self.json_reader.next_null()
    }

    fn read_bool(mut self) -> Result<bool, ReaderError> {
        self.check_skip_name()?;
        self.consumed_value.set(true);
        self.json_reader.next_bool()
    }

    fn read_string(mut self) -> Result<String, ReaderError> {
        self.check_skip_name()?;
        self.consumed_value.set(true);
        self.json_reader.next_string()
    }

    fn read_number<T: FromStr>(mut self) -> Result<Result<T, T::Err>, ReaderError> {
        self.check_skip_name()?;
        self.consumed_value.set(true);
        self.json_reader.next_number()
    }

    fn read_number_as_string(mut self) -> Result<String, ReaderError> {
        self.check_skip_name()?;
        self.consumed_value.set(true);
        self.json_reader.next_number_as_string()
    }

    #[cfg(feature = "serde")]
    fn read_deserialize<'de, D: serde::de::Deserialize<'de>>(
        mut self,
    ) -> Result<D, crate::serde::DeserializerError> {
        self.check_skip_name()?;
        self.consumed_value.set(true);
        self.json_reader.deserialize_next()
    }

    fn skip_value(mut self) -> Result<(), ReaderError> {
        self.check_skip_name()?;
        self.consumed_value.set(true);
        self.json_reader.skip_value()
    }

    fn read_array<T>(
        mut self,
        f: impl FnOnce(&mut ArrayReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        self.check_skip_name()?;
        self.consumed_value.set(true);
        read_array(self.json_reader, f)
    }

    fn read_object_borrowed_names(
        mut self,
        f: impl FnMut(MemberReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        self.check_skip_name()?;
        self.consumed_value.set(true);
        read_object_borrowed_names(self.json_reader, f)
    }

    fn read_object_owned_names(
        mut self,
        f: impl FnMut(String, SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        self.check_skip_name()?;
        self.consumed_value.set(true);
        read_object_owned_names(self.json_reader, f)
    }

    fn read_seeked_multi(
        mut self,
        path: &MultiJsonPath,
        at_least_one_match: bool,
        f: impl FnMut(SingleValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        self.check_skip_name()?;
        self.consumed_value.set(true);
        read_seeked_multi(self.json_reader, path, at_least_one_match, f)
    }
}
