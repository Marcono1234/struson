//! Integration test for a custom `JsonReader` implementation
//!
//! The `JsonReader` implementation here is built on top of serde_json's `Value`.
//! This ensures that the `JsonReader` trait can be implemented by users, and does
//! not depend on something which is only accessible within Struson.
//!
//! **Important:** This code is only for integration test and demonstration purposes;
//! it is not intended to be used in production code.

use crate::custom_reader::JsonValueReader;
use serde_json::json;
use std::io::Read;
use struson::{
    reader::{
        JsonReader, ReaderError, UnexpectedStructureKind, ValueType,
        json_path::{JsonPath, json_path},
    },
    writer::{JsonStreamWriter, JsonWriter},
};

mod custom_reader {
    use serde_json::Value;
    use std::{io::Read, iter::Peekable};
    use struson::{
        reader::{
            JsonReader, JsonReaderPosition, ReaderError, TransferError, UnexpectedStructureKind,
            ValueType, json_path::JsonPathPiece,
        },
        writer::{JsonNumberError, JsonWriter},
    };

    enum StackValue<'a> {
        Array(Peekable<std::slice::Iter<'a, Value>>),
        Object(Peekable<serde_json::map::Iter<'a>>),
    }

    pub struct JsonValueReader<'a> {
        /// Contains the next value to consume
        ///
        /// Either the top-level value, or the next value in arrays or for object members.
        next_value: Option<&'a Value>,
        stack: Vec<StackValue<'a>>,
        /// Whether the reader is currently in a JSON object and expects a name (or end of the JSON object)
        expects_name: bool,
        /// Buffer for string representation of number (to allow returning it as `str`)
        number_str_buf: String,
        is_string_value_reader_active: bool,
        pub(crate) json_path: Vec<JsonPathPiece>,
    }
    impl<'a> JsonValueReader<'a> {
        pub fn new(value: &'a Value) -> Self {
            let initial_nesting_capacity = 16;
            JsonValueReader {
                next_value: Some(value),
                stack: Vec::with_capacity(initial_nesting_capacity),
                expects_name: false,
                number_str_buf: String::new(),
                is_string_value_reader_active: false,
                json_path: Vec::with_capacity(initial_nesting_capacity),
            }
        }
    }

    impl JsonValueReader<'_> {
        fn verify_string_reader_inactive(&self) {
            if self.is_string_value_reader_active {
                panic!("Incorrect reader usage: String value reader is active");
            }
        }

        fn create_error_location(&self) -> JsonReaderPosition {
            self.current_position(true)
        }

        fn begin_value(&mut self, expected: ValueType) -> Result<(), ReaderError> {
            let actual = self.peek()?;
            if actual == expected {
                Ok(())
            } else {
                Err(ReaderError::UnexpectedValueType {
                    expected,
                    actual,
                    location: self.create_error_location(),
                })
            }
        }

        fn end_value(&mut self) {
            if let Some(JsonPathPiece::ArrayItem(index)) = self.json_path.last_mut() {
                *index += 1;
            }
            if let Some(StackValue::Object(_)) = self.stack.last() {
                // Expect the name of the next member
                self.expects_name = true;
            }
        }
    }

    impl JsonReader for JsonValueReader<'_> {
        fn peek(&mut self) -> Result<ValueType, ReaderError> {
            self.verify_string_reader_inactive();
            if self.next_value.is_none() && self.stack.is_empty() {
                panic!("Incorrect reader usage: Value has been consumed already")
            }

            if self.expects_name {
                panic!("Incorrect reader usage: Cannot peek when name is expected");
            }

            if self.next_value.is_none() {
                match self.stack.last_mut().unwrap() {
                    StackValue::Array(iter) => {
                        if let Some(value) = iter.next() {
                            self.next_value = Some(value);
                        } else {
                            return Err(ReaderError::UnexpectedStructure {
                                kind: UnexpectedStructureKind::FewerElementsThanExpected,
                                location: self.create_error_location(),
                            });
                        }
                    }
                    _ => unreachable!(
                        "for JSON object next_name should have put member value as next_value"
                    ),
                }
            }

            Ok(match self.next_value.unwrap() {
                Value::Null => ValueType::Null,
                Value::Bool(_) => ValueType::Boolean,
                Value::Number(_) => ValueType::Number,
                Value::String(_) => ValueType::String,
                Value::Array(_) => ValueType::Array,
                Value::Object(_) => ValueType::Object,
            })
        }

        fn begin_object(&mut self) -> Result<(), ReaderError> {
            self.begin_value(ValueType::Object)?;
            match self.next_value.take().unwrap() {
                Value::Object(map) => self.stack.push(StackValue::Object(map.iter().peekable())),
                _ => unreachable!(),
            }
            // Push name for not yet started first member
            self.json_path
                .push(JsonPathPiece::ObjectMember("<?>".to_owned()));
            self.expects_name = true;

            Ok(())
        }

        fn end_object(&mut self) -> Result<(), ReaderError> {
            if self.next_value.is_some() {
                panic!("Incorrect reader usage: Cannot end object; unconsumed value");
            }
            if let Some(StackValue::Object(iter)) = self.stack.last_mut() {
                if iter.peek().is_some() {
                    Err(ReaderError::UnexpectedStructure {
                        kind: UnexpectedStructureKind::MoreElementsThanExpected,
                        location: self.create_error_location(),
                    })
                } else {
                    self.stack.pop();
                    self.json_path.pop();

                    // Clear `expects_name` because enclosing container (if any) might not be JSON object;
                    // if necessary `end_value()` will set `expects_name = true` again
                    self.expects_name = false;
                    self.end_value();

                    Ok(())
                }
            } else {
                panic!("Incorrect reader usage: Cannot end object; not inside object")
            }
        }

        fn begin_array(&mut self) -> Result<(), ReaderError> {
            self.begin_value(ValueType::Array)?;
            match self.next_value.take().unwrap() {
                Value::Array(vec) => self.stack.push(StackValue::Array(vec.iter().peekable())),
                _ => unreachable!(),
            }
            self.json_path.push(JsonPathPiece::ArrayItem(0));

            Ok(())
        }

        fn end_array(&mut self) -> Result<(), ReaderError> {
            if let Some(StackValue::Array(iter)) = self.stack.last_mut() {
                if iter.peek().is_some() {
                    Err(ReaderError::UnexpectedStructure {
                        kind: UnexpectedStructureKind::MoreElementsThanExpected,
                        location: self.create_error_location(),
                    })
                } else {
                    self.stack.pop();
                    self.json_path.pop();
                    self.end_value();

                    Ok(())
                }
            } else {
                panic!("Incorrect reader usage: Cannot end array; not inside array")
            }
        }

        fn has_next(&mut self) -> Result<bool, ReaderError> {
            self.verify_string_reader_inactive();

            if let Some(stack_value) = self.stack.last_mut() {
                Ok(match stack_value {
                    StackValue::Array(iter) => iter.peek().is_some(),
                    StackValue::Object(iter) => {
                        if self.expects_name {
                            iter.peek().is_some()
                        } else {
                            panic!(
                                "Incorrect reader usage: Cannot check for next when member value is expected"
                            );
                        }
                    }
                })
            } else {
                panic!("Incorrect reader usage: Not inside array or object");
            }
        }

        fn next_name(&mut self) -> Result<&str, ReaderError> {
            if self.expects_name {
                let name;
                match self.stack.last_mut().unwrap() {
                    StackValue::Object(iter) => {
                        if let Some((n, v)) = iter.next() {
                            name = n.as_str();
                            self.next_value = Some(v);
                        } else {
                            return Err(ReaderError::UnexpectedStructure {
                                kind: UnexpectedStructureKind::FewerElementsThanExpected,
                                location: self.create_error_location(),
                            });
                        }
                    }
                    _ => unreachable!("stack should contain Object when expects_name == true"),
                }

                self.expects_name = false;
                if let JsonPathPiece::ObjectMember(path_name) = self.json_path.last_mut().unwrap() {
                    name.clone_into(path_name);
                } else {
                    unreachable!()
                }
                Ok(name)
            } else {
                panic!("Incorrect reader usage: Name is not expected");
            }
        }

        fn next_name_owned(&mut self) -> Result<String, ReaderError> {
            self.next_name().map(str::to_owned)
        }

        fn next_str(&mut self) -> Result<&str, ReaderError> {
            self.begin_value(ValueType::String)?;
            if let Some(Value::String(s)) = self.next_value.take() {
                self.end_value();
                Ok(s.as_str())
            } else {
                unreachable!("begin_value should have verified that value is string")
            }
        }

        fn next_string(&mut self) -> Result<String, ReaderError> {
            self.next_str().map(str::to_owned)
        }

        fn next_string_reader(&mut self) -> Result<impl Read + '_, ReaderError> {
            self.begin_value(ValueType::String)?;
            if let Some(Value::String(s)) = self.next_value.take() {
                self.is_string_value_reader_active = true;
                Ok(StringValueReader {
                    delegate: s.as_bytes(),
                    json_reader: self,
                    reached_end: false,
                })
            } else {
                unreachable!("begin_value should have verified that value is string")
            }
        }

        fn next_number_as_str(&mut self) -> Result<&str, ReaderError> {
            self.begin_value(ValueType::Number)?;
            if let Some(Value::Number(n)) = self.next_value.take() {
                self.end_value();
                // TODO: Is `to_string()` guaranteed to produce valid JSON numbers?
                self.number_str_buf = n.to_string();
                Ok(&self.number_str_buf)
            } else {
                unreachable!("begin_value should have verified that value is number")
            }
        }

        fn next_number_as_string(&mut self) -> Result<String, ReaderError> {
            self.next_number_as_str().map(str::to_owned)
        }

        fn next_bool(&mut self) -> Result<bool, ReaderError> {
            self.begin_value(ValueType::Boolean)?;
            if let Some(Value::Bool(b)) = self.next_value.take() {
                self.end_value();
                Ok(*b)
            } else {
                unreachable!("begin_value should have verified that value is boolean")
            }
        }

        fn next_null(&mut self) -> Result<(), ReaderError> {
            self.begin_value(ValueType::Null)?;
            if let Some(Value::Null) = self.next_value.take() {
                self.end_value();
                Ok(())
            } else {
                unreachable!("begin_value should have verified that value is null")
            }
        }

        #[cfg(feature = "serde")]
        fn deserialize_next<'de, D: serde::Deserialize<'de>>(
            &mut self,
        ) -> Result<D, struson::serde::DeserializerError> {
            // peek here to fail fast if reader is currently not expecting a value
            self.peek()?;
            let mut deserializer = struson::serde::JsonReaderDeserializer::new(self);
            D::deserialize(&mut deserializer)
            // TODO: Verify that value was properly deserialized (only single value; no incomplete array or object)
            //       might not be necessary because Serde's Deserializer API enforces this by consuming `self`, and
            //       JsonReaderDeserializer makes sure JSON arrays and objects are read completely
        }

        fn skip_name(&mut self) -> Result<(), ReaderError> {
            self.next_name()?;
            Ok(())
        }

        fn skip_value(&mut self) -> Result<(), ReaderError> {
            // Peek to place value in `next_value`, and to verify that reader is in correct state to handle value
            // and not for example expects a name
            let value_type = self.peek()?;
            // Call regular value handling method (to match other value consuming methods)
            self.begin_value(value_type)?;
            // Skip by clearing next value
            self.next_value = None;
            // Update reader state
            self.end_value();

            Ok(())
        }

        fn skip_to_top_level(&mut self) -> Result<(), ReaderError> {
            self.verify_string_reader_inactive();

            // Handle expected member value separately because has_next() calls below are not allowed when
            // member value is expected
            if let Some(StackValue::Object(_)) = self.stack.last() {
                if self.next_value.is_some() {
                    self.skip_value()?;
                }
            }

            while let Some(value_type) = self.stack.last() {
                let last_element_index = self.stack.len() - 1;
                match value_type {
                    StackValue::Array(_) => {
                        // Replace with empty iter to allow directly ending array without having to consume remaining values
                        self.stack[last_element_index] = StackValue::Array([].iter().peekable());
                        self.end_array()?;
                    }
                    StackValue::Object(_) => {
                        // TODO: Could probably also implement this more efficiently by replacing `self.stack[last_element_index]`
                        // with empty iter (but cannot be `Map::new().iter()`, because this results in "temporary value dropped while borrowed")
                        while self.has_next()? {
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
            if self.expects_name {
                panic!("Incorrect reader usage: Cannot transfer value when expecting member name");
            }

            let mut depth: u32 = 0;
            loop {
                if depth > 0 && !self.has_next()? {
                    if let StackValue::Array(_) = self.stack.last().unwrap() {
                        self.end_array()?;
                        json_writer.end_array()?;
                    } else {
                        self.end_object()?;
                        json_writer.end_object()?;
                    }
                    depth -= 1;
                } else {
                    if self.expects_name {
                        let name = self.next_name()?;
                        json_writer.name(name)?;
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
                            json_writer.string_value(self.next_str()?)?;
                        }
                        ValueType::Number => {
                            let number = self.next_number_as_str()?;
                            // Should not fail since next_number_as_string would have returned Err for invalid JSON number
                            if let Err(e) = json_writer.number_value_from_string(number) {
                                match e {
                                    JsonNumberError::InvalidNumber(e) => panic!(
                                        "Unexpected: JSON writer rejected valid JSON number '{number}': {e}"
                                    ),
                                    JsonNumberError::IoError(e) => {
                                        return Err(TransferError::WriterError(e));
                                    }
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

        fn consume_trailing_whitespace(self) -> Result<(), ReaderError> {
            self.verify_string_reader_inactive();

            if self.next_value.is_some() || !self.stack.is_empty() {
                panic!("Incorrect reader usage: Value has not been fully consumed")
            }
            Ok(())
        }

        fn current_position(&self, include_path: bool) -> JsonReaderPosition {
            JsonReaderPosition {
                path: if include_path {
                    Some(self.json_path.clone())
                } else {
                    None
                },
                line_pos: None,
                data_pos: None,
            }
        }
    }

    struct StringValueReader<'j, 'a, R: Read> {
        delegate: R,
        json_reader: &'j mut JsonValueReader<'a>,
        reached_end: bool,
    }
    impl<R: Read> Read for StringValueReader<'_, '_, R> {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            if buf.is_empty() || self.reached_end {
                return Ok(0);
            }

            let n = self.delegate.read(buf)?;
            if n == 0 {
                self.reached_end = true;
                self.json_reader.is_string_value_reader_active = false;
                self.json_reader.end_value();
            }
            Ok(n)
        }
    }
}

#[test]
fn read() -> Result<(), Box<dyn std::error::Error>> {
    let json = json!([
        {
            "name1": 1,
            "name2": 2,
        },
        "str1",
        "str2",
        "str3",
        1,
        -2.3,
        4,
        null,
        true,
        false,
    ]);
    let mut json_reader = JsonValueReader::new(&json);

    assert_eq!(ValueType::Array, json_reader.peek()?);
    json_reader.begin_array()?;
    assert!(json_reader.has_next()?);

    json_reader.begin_object()?;
    assert!(json_reader.has_next()?);
    assert_eq!("name1", json_reader.next_name()?);
    assert_eq!(ValueType::Number, json_reader.peek()?);
    assert_eq!("1", json_reader.next_number_as_str()?);
    assert_eq!("name2", json_reader.next_name_owned()?);
    assert_eq!("2", json_reader.next_number_as_str()?);
    assert!(!json_reader.has_next()?);
    json_reader.end_object()?;

    assert_eq!("str1", json_reader.next_str()?);
    assert_eq!("str2", json_reader.next_string()?);

    let mut string = String::new();
    let mut string_reader = json_reader.next_string_reader()?;
    string_reader.read_to_string(&mut string)?;
    drop(string_reader);
    assert_eq!("str3", string);

    assert_eq!("1", json_reader.next_number_as_str()?);
    assert_eq!("-2.3", json_reader.next_number_as_string()?);
    assert_eq!(4_u32, json_reader.next_number::<u32>()??);

    json_reader.next_null()?;

    assert_eq!(true, json_reader.next_bool()?);
    assert_eq!(false, json_reader.next_bool()?);

    assert!(!json_reader.has_next()?);
    json_reader.end_array()?;
    json_reader.consume_trailing_whitespace()?;
    Ok(())
}

#[test]
fn skip() -> Result<(), Box<dyn std::error::Error>> {
    let json = json!([
        1,
        null,
        2,
        "test",
        3,
        [
            true,
            false,
        ],
        4,
        {
            "name1": 1,
            "name2": 2,
        },
        5,
        {
            "name1": 3,
            "name2": 4,
        },
        6,
    ]);
    let mut json_reader = JsonValueReader::new(&json);

    json_reader.begin_array()?;
    assert_eq!("1", json_reader.next_number_as_str()?);
    json_reader.skip_value()?;

    assert_eq!("2", json_reader.next_number_as_str()?);
    json_reader.skip_value()?;

    assert_eq!("3", json_reader.next_number_as_str()?);
    json_reader.skip_value()?;

    assert_eq!("4", json_reader.next_number_as_str()?);
    json_reader.begin_object()?;
    json_reader.skip_name()?;
    assert_eq!("1", json_reader.next_number_as_str()?);
    assert_eq!("name2", json_reader.next_name()?);
    json_reader.skip_value()?;
    json_reader.end_object()?;

    assert_eq!("5", json_reader.next_number_as_str()?);
    json_reader.skip_value()?;

    assert_eq!("6", json_reader.next_number_as_str()?);
    Ok(())
}

#[test]
fn seek_to() -> Result<(), Box<dyn std::error::Error>> {
    let json = json!([
        true,
        false,
        {
            "name1": null,
            "name2": [
                {
                    "name3": 4,
                },
            ],
            "name4": true,
        },
        1,
    ]);
    let mut json_reader = JsonValueReader::new(&json);
    json_reader.seek_to(&json_path![2, "name2", 0, "name3"])?;
    assert_eq!(
        json_path![2, "name2", 0, "name3"],
        &json_reader.json_path as &JsonPath
    );
    assert_eq!("4", json_reader.next_number_as_str()?);

    json_reader.skip_to_top_level()?;
    json_reader.consume_trailing_whitespace()?;
    Ok(())
}

#[test]
fn transfer() -> Result<(), Box<dyn std::error::Error>> {
    let json = json!([
        true,
        false,
        {
            "name1": null,
            "name2": [
                {
                    "name3": 4,
                },
            ],
            "name4": true,
        },
        1,
    ]);
    let mut json_reader = JsonValueReader::new(&json);

    let mut writer = Vec::new();
    let mut json_writer = JsonStreamWriter::new(&mut writer);
    json_reader.transfer_to(&mut json_writer)?;
    json_reader.consume_trailing_whitespace()?;
    json_writer.finish_document()?;

    assert_eq!(
        "[true,false,{\"name1\":null,\"name2\":[{\"name3\":4}],\"name4\":true},1]",
        String::from_utf8(writer)?
    );
    Ok(())
}

#[test]
fn unexpected_structure() -> Result<(), Box<dyn std::error::Error>> {
    macro_rules! assert_unexpected_structure {
        ($value:expr, $kind:pat_param, {$assertion:expr}) => {
            // Separate block to drop result of `next_string_reader` properly after assertion
            {
                let value = $value;
                match value {
                    Err(ReaderError::UnexpectedStructure { kind: $kind, .. }) => $assertion,
                    // Note: Cannot include `{value:?}` because for `next_string_reader` value does not implement Debug
                    _ => panic!("Unexpected value"),
                }
            }
        };
        ($value:expr, $kind:pat_param) => {
            assert_unexpected_structure!($value, $kind, { () });
        };
    }

    let json = json!([1]);
    let mut json_reader = JsonValueReader::new(&json);
    json_reader.begin_array()?;
    assert_unexpected_structure!(
        json_reader.end_array(),
        UnexpectedStructureKind::MoreElementsThanExpected
    );
    json_reader.skip_value()?;
    assert_unexpected_structure!(
        json_reader.peek(),
        UnexpectedStructureKind::FewerElementsThanExpected
    );
    assert_unexpected_structure!(
        json_reader.skip_value(),
        UnexpectedStructureKind::FewerElementsThanExpected
    );
    assert_unexpected_structure!(
        json_reader.next_bool(),
        UnexpectedStructureKind::FewerElementsThanExpected
    );
    assert_unexpected_structure!(
        json_reader.next_string_reader(),
        UnexpectedStructureKind::FewerElementsThanExpected
    );
    json_reader.end_array()?;
    json_reader.consume_trailing_whitespace()?;

    let json = json!({"a": 1});
    let mut json_reader = JsonValueReader::new(&json);
    json_reader.begin_object()?;
    assert_unexpected_structure!(
        json_reader.end_object(),
        UnexpectedStructureKind::MoreElementsThanExpected
    );
    json_reader.skip_name()?;
    json_reader.skip_value()?;
    assert_unexpected_structure!(
        json_reader.skip_name(),
        UnexpectedStructureKind::FewerElementsThanExpected
    );
    assert_unexpected_structure!(
        json_reader.next_name(),
        UnexpectedStructureKind::FewerElementsThanExpected
    );
    json_reader.end_object()?;
    json_reader.consume_trailing_whitespace()?;

    let json = json!([]);
    let mut json_reader = JsonValueReader::new(&json);
    assert_unexpected_structure!(
        json_reader.seek_to(&json_path![0]),
        UnexpectedStructureKind::TooShortArray { expected_index: 0 }
    );

    let json = json!({});
    let mut json_reader = JsonValueReader::new(&json);
    assert_unexpected_structure!(
        json_reader.seek_to(&json_path!["a"]),
        UnexpectedStructureKind::MissingObjectMember { member_name },
        { assert_eq!("a", member_name) }
    );

    Ok(())
}

#[test]
fn unexpected_value_type() -> Result<(), Box<dyn std::error::Error>> {
    macro_rules! assert_unexpected_value_type {
        ($value:expr, $expected:ident, $actual:ident) => {
            // Separate block to drop result of `next_string_reader` properly after assertion
            {
                let value = $value;
                match value {
                    Err(ReaderError::UnexpectedValueType {
                        expected: ValueType::$expected,
                        actual: ValueType::$actual,
                        ..
                    }) => {}
                    // Note: Cannot include `{value:?}` because for `next_string_reader` value does not implement Debug
                    _ => panic!("Unexpected value"),
                }
            }
        };
    }

    let json = json!(1);
    let mut json_reader = JsonValueReader::new(&json);
    assert_unexpected_value_type!(json_reader.begin_array(), Array, Number);
    assert_unexpected_value_type!(json_reader.begin_object(), Object, Number);
    assert_unexpected_value_type!(json_reader.next_str(), String, Number);
    assert_unexpected_value_type!(json_reader.next_string_reader(), String, Number);

    assert_unexpected_value_type!(json_reader.seek_to(&json_path![0]), Array, Number);
    assert_unexpected_value_type!(json_reader.seek_to(&json_path!["a"]), Object, Number);

    Ok(())
}

#[cfg(feature = "serde")]
#[test]
fn deserialize() -> Result<(), Box<dyn std::error::Error>> {
    use serde::Deserialize;

    #[derive(Deserialize, PartialEq, Debug)]
    struct CustomStruct {
        a: u32,
    }

    let json = json!({
        "a": 1
    });
    let mut json_reader = JsonValueReader::new(&json);

    let deserialized: CustomStruct = json_reader.deserialize_next()?;
    assert_eq!(CustomStruct { a: 1 }, deserialized);

    json_reader.consume_trailing_whitespace()?;
    Ok(())
}
