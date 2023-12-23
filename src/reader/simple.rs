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

use std::{cell::RefCell, error::Error, io::Read, rc::Rc, str::FromStr};

use crate::reader::{json_path::JsonPath, JsonReader, JsonStreamReader, ReaderError, ValueType};

/// Reader for a JSON value
pub trait ValueReader<J: JsonReader> {
    /// Peeks at the type of the next JSON value, without consuming it
    fn peek(&mut self) -> Result<ValueType, ReaderError>;

    /// Consumes a JSON null value
    fn next_null(self) -> Result<(), ReaderError>;

    /// Consumes and returns a JSON boolean value
    fn next_bool(self) -> Result<bool, ReaderError>;

    /// Consumes and returns a JSON string value
    fn next_string(self) -> Result<String, ReaderError>;

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
    /// let number: u64 = json_reader.next_number()??;
    /// assert_eq!(number, 12);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn next_number<T: FromStr>(self) -> Result<Result<T, T::Err>, ReaderError>;

    /// Consumes and returns the string representation of a JSON number value
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// let json_reader = SimpleJsonReader::new("1.2e3".as_bytes());
    /// let number_string = json_reader.next_number_as_string()?;
    /// assert_eq!(number_string, "1.2e3");
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn next_number_as_string(self) -> Result<String, ReaderError>;

    /// Deserializes a Serde [`Deserialize`](serde::de::Deserialize) from the next value
    ///
    /// This method is part of the optional Serde integration feature, see the
    /// [`serde`](crate::serde) module of this crate for more information.
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
    /// let value: MyStruct = json_reader.deserialize_next()?;
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
    fn deserialize_next<'de, D: serde::de::Deserialize<'de>>(
        self,
    ) -> Result<D, crate::serde::DeserializerError>;

    /// Skips the next JSON value
    ///
    /// If the value is a JSON array or object, all the nested values will be skipped as well.
    /// This method is usually more efficient than reading the next JSON value using one of
    /// the other methods, but discarding the read result afterwards.
    fn skip_next(self) -> Result<(), ReaderError>;

    /// Consumes a JSON array
    ///
    /// This method is useful when arrays of fixed size or with heterogenous item types are read;
    /// otherwise prefer [`next_array_items`](Self::next_array_items).
    ///
    /// If the exact size is not known in advance, [`ArrayReader::has_next`] can be used to
    /// check if there are more items in the JSON array. If the value types are not known in
    /// advance, [`ArrayReader::peek`](ValueReader::peek) can be used to peek at next item
    /// (optionally calling `has_next` before to make sure there is actually a next item).
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// let json_reader = SimpleJsonReader::new("[1, 2, 3]".as_bytes());
    /// let point: (u64, u64, u64) = json_reader.next_array(|array_reader| {
    ///     let x = array_reader.next_number()??;
    ///     let y = array_reader.next_number()??;
    ///     let z = array_reader.next_number()??;
    ///     Ok((x, y, z))
    /// })?;
    /// assert_eq!(point, (1, 2, 3));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn next_array<T>(
        self,
        f: impl FnOnce(&mut ArrayReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>>;

    /// Consumes a JSON array and all of its items
    ///
    /// This method is useful when arrays with varying size and homogenous item type are read;
    /// otherwise prefer [`next_array`](Self::next_array).
    ///
    /// The function `f` is called repeatedly for all items of the JSON array, if any.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// let json_reader = SimpleJsonReader::new(r#"["a", "short", "example"]"#.as_bytes());
    /// let mut words = Vec::<String>::new();
    /// json_reader.next_array_items(|item_reader| {
    ///     let word = item_reader.next_string()?;
    ///     words.push(word);
    ///     Ok(())
    /// })?;
    /// assert_eq!(words, vec!["a", "short", "example"]);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn next_array_items(
        self,
        mut f: impl FnMut(ArrayItemReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>>
    where
        Self: Sized,
    {
        self.next_array(|array_reader| {
            while array_reader.has_next()? {
                let item_reader = ArrayItemReader {
                    json_reader: array_reader.json_reader,
                };
                f(item_reader)?;
            }
            Ok(())
        })
    }

    /// Consumes a JSON object and all of its members
    ///
    /// The function `f` is called repeatedly for all members of the JSON object, if any. It takes
    /// the member name as first argument and a [`MemberValueReader`] for reading the member value
    /// as second argument.
    ///
    /// If the function returns `Ok` but did not consume the value of the member, either by
    /// reading it (e.g. using [`next_bool`](Self::next_bool)) or by using [`skip_next`](Self::skip_next),
    /// the value will be skipped automatically.
    ///
    /// # Examples
    /// ```
    /// # use std::collections::HashMap;
    /// # use struson::reader::simple::*;
    /// let json_reader = SimpleJsonReader::new(r#"{"a": 1, "b": 2}"#.as_bytes());
    /// let mut map = HashMap::<String, u64>::new();
    /// json_reader.next_object(|name, value_reader| {
    ///     let member_value = value_reader.next_number()??;
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
    fn next_object(
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

fn read_object<J: JsonReader>(
    json_reader: &mut J,
    mut f: impl FnMut(String, MemberValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
) -> Result<(), Box<dyn Error>> {
    json_reader.begin_object()?;
    while json_reader.has_next()? {
        let name = json_reader.next_name_owned()?;
        let consumed_value = Rc::new(RefCell::new(false));
        let member_value_reader = MemberValueReader {
            json_reader,
            consumed_value: Rc::clone(&consumed_value),
        };
        f(name, member_value_reader)?;
        // If the function did not consume the value, skip it
        if !*consumed_value.borrow() {
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
/// json_reader.next_array_items(|item_reader| {
///     let word = item_reader.next_string()?;
///     words.push(word);
///     Ok(())
/// })?;
/// assert_eq!(words, vec!["a", "short", "example"]);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
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
    /// let value = json_reader.next_string()?;
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
    fn peek(&mut self) -> Result<ValueType, ReaderError> {
        self.json_reader.peek()
    }

    fn next_null(mut self) -> Result<(), ReaderError> {
        self.json_reader.next_null()?;
        self.finish()
    }

    fn next_bool(mut self) -> Result<bool, ReaderError> {
        let result = self.json_reader.next_bool()?;
        self.finish()?;
        Ok(result)
    }

    fn next_string(mut self) -> Result<String, ReaderError> {
        let result = self.json_reader.next_string()?;
        self.finish()?;
        Ok(result)
    }

    fn next_number<T: FromStr>(mut self) -> Result<Result<T, T::Err>, ReaderError> {
        let result = self.json_reader.next_number()?;
        self.finish()?;
        Ok(result)
    }

    fn next_number_as_string(mut self) -> Result<String, ReaderError> {
        let result = self.json_reader.next_number_as_string()?;
        self.finish()?;
        Ok(result)
    }

    #[cfg(feature = "serde")]
    fn deserialize_next<'de, D: serde::de::Deserialize<'de>>(
        mut self,
    ) -> Result<D, crate::serde::DeserializerError> {
        let result = self.json_reader.deserialize_next()?;
        self.finish()?;
        Ok(result)
    }

    fn skip_next(mut self) -> Result<(), ReaderError> {
        self.json_reader.skip_value()?;
        self.finish()
    }

    fn next_array<T>(
        mut self,
        f: impl FnOnce(&mut ArrayReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        let result = read_array(&mut self.json_reader, f)?;
        self.finish()?;
        Ok(result)
    }

    fn next_object(
        mut self,
        f: impl FnMut(String, MemberValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        read_object(&mut self.json_reader, f)?;
        self.finish()?;
        Ok(())
    }
}

/// Reader for an arbitrary amount of JSON array items
pub struct ArrayReader<'a, J: JsonReader> {
    json_reader: &'a mut J,
}
impl<J: JsonReader> ArrayReader<'_, J> {
    /// Checks if there is a next item in the JSON array, without consuming it
    ///
    /// Returns `true` if there is a next element, `false` otherwise. This method can be
    /// useful as condition of a `while` loop when processing a JSON array of unknown size.
    ///
    /// # Examples
    /// ```
    /// # use struson::reader::simple::*;
    /// let json_reader = SimpleJsonReader::new("[1, 2]".as_bytes());
    /// json_reader.next_array(|array_reader| {
    ///     while array_reader.has_next()? {
    ///         let value = array_reader.next_number_as_string()?;
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
    fn peek(&mut self) -> Result<ValueType, ReaderError> {
        self.json_reader.peek()
    }

    fn next_null(self) -> Result<(), ReaderError> {
        self.json_reader.next_null()
    }

    fn next_bool(self) -> Result<bool, ReaderError> {
        self.json_reader.next_bool()
    }

    fn next_string(self) -> Result<String, ReaderError> {
        self.json_reader.next_string()
    }

    fn next_number<T: FromStr>(self) -> Result<Result<T, T::Err>, ReaderError> {
        self.json_reader.next_number()
    }

    fn next_number_as_string(self) -> Result<String, ReaderError> {
        self.json_reader.next_number_as_string()
    }

    #[cfg(feature = "serde")]
    fn deserialize_next<'de, D: serde::de::Deserialize<'de>>(
        self,
    ) -> Result<D, crate::serde::DeserializerError> {
        self.json_reader.deserialize_next()
    }

    fn skip_next(self) -> Result<(), ReaderError> {
        self.json_reader.skip_value()
    }

    fn next_array<T>(
        self,
        f: impl FnOnce(&mut ArrayReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        read_array(self.json_reader, f)
    }

    fn next_object(
        self,
        f: impl FnMut(String, MemberValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        read_object(self.json_reader, f)
    }
}

/// Reader for a single JSON array item
pub struct ArrayItemReader<'a, J: JsonReader> {
    json_reader: &'a mut J,
}
impl<J: JsonReader> ValueReader<J> for ArrayItemReader<'_, J> {
    fn peek(&mut self) -> Result<ValueType, ReaderError> {
        self.json_reader.peek()
    }

    fn next_null(self) -> Result<(), ReaderError> {
        self.json_reader.next_null()
    }

    fn next_bool(self) -> Result<bool, ReaderError> {
        self.json_reader.next_bool()
    }

    fn next_string(self) -> Result<String, ReaderError> {
        self.json_reader.next_string()
    }

    fn next_number<T: FromStr>(self) -> Result<Result<T, T::Err>, ReaderError> {
        self.json_reader.next_number()
    }

    fn next_number_as_string(self) -> Result<String, ReaderError> {
        self.json_reader.next_number_as_string()
    }

    #[cfg(feature = "serde")]
    fn deserialize_next<'de, D: serde::de::Deserialize<'de>>(
        self,
    ) -> Result<D, crate::serde::DeserializerError> {
        self.json_reader.deserialize_next()
    }

    fn skip_next(self) -> Result<(), ReaderError> {
        self.json_reader.skip_value()
    }

    fn next_array<T>(
        self,
        f: impl FnOnce(&mut ArrayReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        read_array(self.json_reader, f)
    }

    fn next_object(
        self,
        f: impl FnMut(String, MemberValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        read_object(self.json_reader, f)
    }
}

/// Reader for a JSON object member value
///
/// That is, for a JSON object `{"a": 1}`, this reader would read the value `1`.
pub struct MemberValueReader<'a, J: JsonReader> {
    json_reader: &'a mut J,
    consumed_value: Rc<RefCell<bool>>,
}
impl<J: JsonReader> ValueReader<J> for MemberValueReader<'_, J> {
    fn peek(&mut self) -> Result<ValueType, ReaderError> {
        self.json_reader.peek()
    }

    fn next_null(self) -> Result<(), ReaderError> {
        *self.consumed_value.borrow_mut() = true;
        self.json_reader.next_null()
    }

    fn next_bool(self) -> Result<bool, ReaderError> {
        *self.consumed_value.borrow_mut() = true;
        self.json_reader.next_bool()
    }

    fn next_string(self) -> Result<String, ReaderError> {
        *self.consumed_value.borrow_mut() = true;
        self.json_reader.next_string()
    }

    fn next_number<T: FromStr>(self) -> Result<Result<T, T::Err>, ReaderError> {
        *self.consumed_value.borrow_mut() = true;
        self.json_reader.next_number()
    }

    fn next_number_as_string(self) -> Result<String, ReaderError> {
        *self.consumed_value.borrow_mut() = true;
        self.json_reader.next_number_as_string()
    }

    #[cfg(feature = "serde")]
    fn deserialize_next<'de, D: serde::de::Deserialize<'de>>(
        self,
    ) -> Result<D, crate::serde::DeserializerError> {
        *self.consumed_value.borrow_mut() = true;
        self.json_reader.deserialize_next()
    }

    fn skip_next(self) -> Result<(), ReaderError> {
        *self.consumed_value.borrow_mut() = true;
        self.json_reader.skip_value()
    }

    fn next_array<T>(
        self,
        f: impl FnOnce(&mut ArrayReader<'_, J>) -> Result<T, Box<dyn Error>>,
    ) -> Result<T, Box<dyn Error>> {
        *self.consumed_value.borrow_mut() = true;
        read_array(self.json_reader, f)
    }

    fn next_object(
        self,
        f: impl FnMut(String, MemberValueReader<'_, J>) -> Result<(), Box<dyn Error>>,
    ) -> Result<(), Box<dyn Error>> {
        *self.consumed_value.borrow_mut() = true;
        read_object(self.json_reader, f)
    }
}
