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

use crate::reader::{json_path::JsonPath, JsonReader, JsonStreamReader, ReaderError, ValueType};

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
        mut f: impl FnMut(ArrayItemReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>>
    where
        Self: Sized,
    {
        self.read_array(|array_reader| {
            while array_reader.has_next()? {
                let consumed_item = Rc::new(Cell::new(false));
                let item_reader = ArrayItemReader {
                    json_reader: array_reader.json_reader,
                    consumed_item: Rc::clone(&consumed_item),
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
    /// the member name as first argument and a [`MemberValueReader`] for reading the member value
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
        f: impl FnMut(String, MemberValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
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
    mut f: impl FnMut(String, MemberValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
) -> Result<(), Box<dyn Error>> {
    json_reader.begin_object()?;
    while json_reader.has_next()? {
        let name = json_reader.next_name_owned()?;
        let consumed_value = Rc::new(Cell::new(false));
        let member_value_reader = MemberValueReader {
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
    /// at 0) index 2.
    ///
    /// Seeking to a specific location can be useful when parts of the processed JSON document
    /// are not relevant for the application processing it.
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
     * and objects
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
        f: impl FnMut(String, MemberValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        read_object_owned_names(&mut self.json_reader, f)?;
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
        f: impl FnMut(String, MemberValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        read_object_owned_names(self.json_reader, f)
    }
}

/// Reader for a single JSON array item
///
/// This struct is used by [`ValueReader::read_array_items`].
#[derive(Debug)]
pub struct ArrayItemReader<'a, J: JsonReader> {
    json_reader: &'a mut J,
    consumed_item: Rc<Cell<bool>>,
}
impl<J: JsonReader> ValueReader<J> for ArrayItemReader<'_, J> {
    fn peek_value(&mut self) -> Result<ValueType, ReaderError> {
        self.json_reader.peek()
    }

    fn read_null(self) -> Result<(), ReaderError> {
        self.consumed_item.set(true);
        self.json_reader.next_null()
    }

    fn read_bool(self) -> Result<bool, ReaderError> {
        self.consumed_item.set(true);
        self.json_reader.next_bool()
    }

    fn read_string(self) -> Result<String, ReaderError> {
        self.consumed_item.set(true);
        self.json_reader.next_string()
    }

    fn read_number<T: FromStr>(self) -> Result<Result<T, T::Err>, ReaderError> {
        self.consumed_item.set(true);
        self.json_reader.next_number()
    }

    fn read_number_as_string(self) -> Result<String, ReaderError> {
        self.consumed_item.set(true);
        self.json_reader.next_number_as_string()
    }

    #[cfg(feature = "serde")]
    fn read_deserialize<'de, D: serde::de::Deserialize<'de>>(
        self,
    ) -> Result<D, crate::serde::DeserializerError> {
        self.consumed_item.set(true);
        self.json_reader.deserialize_next()
    }

    fn skip_value(self) -> Result<(), ReaderError> {
        self.consumed_item.set(true);
        self.json_reader.skip_value()
    }

    fn read_array<T>(
        self,
        f: impl FnOnce(&mut ArrayReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        self.consumed_item.set(true);
        read_array(self.json_reader, f)
    }

    fn read_object_borrowed_names(
        self,
        f: impl FnMut(MemberReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        self.consumed_item.set(true);
        read_object_borrowed_names(self.json_reader, f)
    }

    fn read_object_owned_names(
        self,
        f: impl FnMut(String, MemberValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        self.consumed_item.set(true);
        read_object_owned_names(self.json_reader, f)
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
        f: impl FnMut(String, MemberValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        self.check_skip_name()?;
        self.consumed_value.set(true);
        read_object_owned_names(self.json_reader, f)
    }
}

/// Reader for a JSON object member value
///
/// That is, for a JSON object `{"a": 1}`, this reader can be used to read the value `1`.
///
/// This struct is used by [`ValueReader::read_object_owned_names`].
#[derive(Debug)]
pub struct MemberValueReader<'a, J: JsonReader> {
    json_reader: &'a mut J,
    consumed_value: Rc<Cell<bool>>,
}
impl<J: JsonReader> ValueReader<J> for MemberValueReader<'_, J> {
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
        f: impl FnMut(String, MemberValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        self.consumed_value.set(true);
        read_object_owned_names(self.json_reader, f)
    }
}
