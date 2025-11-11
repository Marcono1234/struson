//! Integration test for a custom `JsonReader` implementation which reads
//! partial / incomplete JSON data
//!
//! This code was originally created for https://github.com/Marcono1234/struson/discussions/19#discussioncomment-7415830
//!
//! **Important:** This code is only for integration test and demonstration purposes;
//! it is not intended to be used in production code.

#![cfg(feature = "serde")]

use serde::Deserialize;
use struson::{
    reader::{
        JsonReader, JsonReaderPosition, JsonStreamReader, JsonSyntaxError, LinePosition,
        ReaderError, SyntaxErrorKind, TransferError, UnexpectedStructureKind, ValueType,
    },
    serde::{DeserializerError, JsonReaderDeserializer},
    writer::JsonWriter,
};

#[derive(Debug, PartialEq)]
enum PeekedValue {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    /// Peeked array start, but has not been consumed yet
    PeekedArray,
    /// Peeked object start, but has not been consumed yet
    PeekedObject,
}
impl PeekedValue {
    fn get_value_type(&self) -> ValueType {
        match self {
            PeekedValue::Null => ValueType::Null,
            PeekedValue::Bool(_) => ValueType::Boolean,
            PeekedValue::Number(_) => ValueType::Number,
            PeekedValue::String(_) => ValueType::String,
            PeekedValue::PeekedArray => ValueType::Array,
            PeekedValue::PeekedObject => ValueType::Object,
        }
    }
}

struct PartialJsonReader<J: JsonReader> {
    delegate: J,
    reached_eof: bool,
    /// Stack which is expanded every time an array or object is opened;
    /// values are `true` if object, `false` if array
    is_in_object: Vec<bool>,
    /// Temporarily holding string value or name to allow returning reference to it
    string_buf: String,
    peeked_name_pos: Option<JsonReaderPosition>,
    peeked_name: Option<String>,
    peeked_value_pos: Option<JsonReaderPosition>,
    peeked_value: Option<PeekedValue>,
    after_peeked_pos: JsonReaderPosition,
}

impl<J: JsonReader> PartialJsonReader<J> {
    pub fn new(delegate: J) -> Self {
        let initial_pos = delegate.current_position(false);
        PartialJsonReader {
            delegate,
            reached_eof: false,
            is_in_object: Vec::new(),
            string_buf: String::new(),
            peeked_name_pos: None,
            peeked_name: None,
            peeked_value_pos: None,
            peeked_value: None,
            after_peeked_pos: initial_pos,
        }
    }
}

impl<J: JsonReader> PartialJsonReader<J> {
    fn provident_current_position(&mut self) -> JsonReaderPosition {
        // For now don't include path for better performance since this method is called providently
        // even if peeking value succeeds and position will be discarded
        let include_path = false;
        self.delegate.current_position(include_path)
    }

    fn peek_value(&mut self) -> Result<ValueType, ReaderError> {
        let peeked = self.delegate.peek()?;
        self.peeked_value_pos = Some(self.provident_current_position());

        self.peeked_value = Some(match peeked {
            ValueType::Array => PeekedValue::PeekedArray,
            ValueType::Object => PeekedValue::PeekedObject,
            ValueType::String => {
                let v = PeekedValue::String(self.delegate.next_string()?);
                self.after_peeked_pos = self.provident_current_position();
                v
            }
            ValueType::Number => {
                let v = PeekedValue::Number(self.delegate.next_number_as_string()?);
                // For number must make sure complete number was processed; for example
                // `1` might actually be `1.2` or `12`

                // Only works for non-top-level value; for top-level value cannot know if number is complete
                if !self.is_in_object.is_empty() {
                    // Trigger EOF error in case nothing follows after last char of number
                    let _ = self.delegate.has_next()?;
                }
                self.after_peeked_pos = self.provident_current_position();
                v
            }
            ValueType::Boolean => {
                let v = PeekedValue::Bool(self.delegate.next_bool()?);
                self.after_peeked_pos = self.provident_current_position();
                v
            }
            ValueType::Null => {
                self.delegate.next_null()?;
                self.after_peeked_pos = self.provident_current_position();
                PeekedValue::Null
            }
        });
        Ok(peeked)
    }

    fn has_next_impl(&mut self) -> Result<bool, ReaderError> {
        if self.delegate.has_next()? {
            // Must peek next array item / object member

            if let Some(true) = self.is_in_object.last() {
                self.peeked_name_pos = Some(self.provident_current_position());
                self.peeked_name = Some(self.delegate.next_name_owned()?);
            }

            self.peek_value()?;
            Ok(true)
        } else {
            Ok(false)
        }
    }
}

macro_rules! consume_expected_value {
    ($self:ident, $expected:pat_param => $consumer:expr, $expected_type:ident) => {{
        // Populate `self.peeked_value` (or fail if there is no next value)
        let _ = $self.peek()?;

        let p = $self.peeked_value.take().unwrap();
        if let $expected = p {
            Ok($consumer)
        } else {
            let actual_type = p.get_value_type();

            // Put back unexpected value
            $self.peeked_value = Some(p);

            Err(ReaderError::UnexpectedValueType {
                expected: ValueType::$expected_type,
                actual: actual_type,
                location: $self.peeked_value_pos.clone().unwrap(),
            })
        }
    }};
}

/*
 * This implementation is incomplete:
 * - multiple methods contain `unimplemented!()`
 * - correct API usage is not properly enforced, e.g. it might be possible to consume
 *   an object member value before its name
 * - retrying on any error type may cause unspecified behavior (even the ones for which JsonReader says
 *   it is safe to retry)
 */
impl<J: JsonReader> JsonReader for PartialJsonReader<J> {
    fn peek(&mut self) -> Result<ValueType, ReaderError> {
        // If called for top-level value and value has not peeked yet, peek at it here
        if self.is_in_object.is_empty() && self.peeked_value.is_none() {
            return self.peek_value();
        }

        if self.has_next()? {
            let p = self.peeked_value.as_ref().unwrap();
            Ok(p.get_value_type())
        } else {
            Err(ReaderError::UnexpectedStructure {
                kind: UnexpectedStructureKind::FewerElementsThanExpected,
                location: self.current_position(true),
            })
        }
    }

    fn begin_object(&mut self) -> Result<(), ReaderError> {
        consume_expected_value!(
            self,
            PeekedValue::PeekedObject => {
                self.is_in_object.push(true);
                self.delegate.begin_object()?;
                self.after_peeked_pos = self.provident_current_position();
            },
            Object
        )
    }

    fn end_object(&mut self) -> Result<(), ReaderError> {
        match self.is_in_object.last() {
            Some(true) => {}
            // Covers `None` (neither in array nor object), and `Some(false)` (in array)
            _ => panic!("not inside object"),
        }

        if self.has_next()? {
            return Err(ReaderError::UnexpectedStructure {
                kind: UnexpectedStructureKind::MoreElementsThanExpected,
                location: self.current_position(true),
            });
        }

        if self.reached_eof {
            self.is_in_object.pop();
            Ok(())
        } else {
            self.delegate.end_object()?;
            // Only pop after delegate `end_object()` was successful, to allow retry if it fails with MoreElementsThanExpected
            self.is_in_object.pop();
            self.after_peeked_pos = self.provident_current_position();
            Ok(())
        }
    }

    fn begin_array(&mut self) -> Result<(), ReaderError> {
        consume_expected_value!(
            self,
            PeekedValue::PeekedArray => {
                self.is_in_object.push(false);
                self.delegate.begin_array()?;
                self.after_peeked_pos = self.provident_current_position();
            },
            Array
        )
    }

    fn end_array(&mut self) -> Result<(), ReaderError> {
        match self.is_in_object.last() {
            Some(false) => {}
            // Covers `None` (neither in array nor object), and `Some(true)` (in object)
            _ => panic!("not inside array"),
        }

        if self.has_next()? {
            return Err(ReaderError::UnexpectedStructure {
                kind: UnexpectedStructureKind::MoreElementsThanExpected,
                location: self.current_position(true),
            });
        }

        if self.reached_eof {
            self.is_in_object.pop();
            Ok(())
        } else {
            self.delegate.end_array()?;
            // Only pop after delegate `end_array()` was successful, to allow retry if it fails with MoreElementsThanExpected
            self.is_in_object.pop();
            self.after_peeked_pos = self.provident_current_position();
            Ok(())
        }
    }

    fn has_next(&mut self) -> Result<bool, ReaderError> {
        if self.reached_eof {
            Ok(false)
        } else if self.peeked_name.is_some() || self.peeked_value.is_some() {
            Ok(true)
        } else {
            match self.has_next_impl() {
                // JsonStreamReader currently reports not only `SyntaxErrorKind::IncompleteDocument`
                // on unexpected EOF, but also other errors, such as `InvalidLiteral`
                Err(ReaderError::SyntaxError(JsonSyntaxError { .. })) => {
                    self.reached_eof = true;
                    // Clear the peeked name, if any, to avoid accidentally consuming it despite the member
                    // value being missing
                    self.peeked_name.take();
                    Ok(false)
                }
                // Propagate any other errors, or success result
                r => r,
            }
        }
    }

    fn next_name(&mut self) -> Result<&str, ReaderError> {
        self.string_buf = self.next_name_owned()?;
        Ok(&self.string_buf)
    }

    fn next_name_owned(&mut self) -> Result<String, ReaderError> {
        match self.is_in_object.last() {
            Some(true) => {}
            // Covers `None` (neither in array nor object), and `Some(false)` (in array)
            _ => panic!("not inside object"),
        }

        if self.has_next()? {
            Ok(self.peeked_name.take().unwrap())
        } else {
            Err(ReaderError::UnexpectedStructure {
                kind: UnexpectedStructureKind::FewerElementsThanExpected,
                location: self.current_position(true),
            })
        }
    }

    fn next_str(&mut self) -> Result<&str, ReaderError> {
        self.string_buf = self.next_string()?;
        Ok(&self.string_buf)
    }

    fn next_string(&mut self) -> Result<String, ReaderError> {
        consume_expected_value!(
            self,
            PeekedValue::String(s) => s,
            String
        )
    }

    fn next_string_reader(&mut self) -> Result<impl std::io::Read + '_, ReaderError> {
        unimplemented!();
        // Unreachable; allow the compiler to infer the type of `impl std::io::Read`
        #[expect(unreachable_code)]
        Ok(std::io::empty())
    }

    fn next_number_as_str(&mut self) -> Result<&str, ReaderError> {
        self.string_buf = self.next_number_as_string()?;
        Ok(&self.string_buf)
    }

    fn next_number_as_string(&mut self) -> Result<String, ReaderError> {
        consume_expected_value!(
            self,
            PeekedValue::Number(s) => s,
            Number
        )
    }

    fn next_bool(&mut self) -> Result<bool, ReaderError> {
        consume_expected_value!(
            self,
            PeekedValue::Bool(b) => b,
            Boolean
        )
    }

    fn next_null(&mut self) -> Result<(), ReaderError> {
        consume_expected_value!(
            self,
            PeekedValue::Null => (),
            Null
        )
    }

    fn deserialize_next<'de, D: Deserialize<'de>>(&mut self) -> Result<D, DeserializerError> {
        let mut deserializer = JsonReaderDeserializer::new(self);
        D::deserialize(&mut deserializer)
    }

    fn skip_name(&mut self) -> Result<(), ReaderError> {
        let _ = self.next_name()?;
        Ok(())
    }

    // Important: This is implemented recursively; could lead to stack overflow for deeply nested JSON
    fn skip_value(&mut self) -> Result<(), ReaderError> {
        // Populate `self.peeked_value` (or fail if there is no next value)
        let _ = self.peek()?;

        match self.peeked_value.as_ref().unwrap() {
            // For array and object need to manually skip value here by delegating to other
            // methods to handle EOF properly; cannot delegate to underlying JSON reader
            PeekedValue::PeekedArray => {
                self.begin_array()?;
                while self.has_next()? {
                    self.skip_value()?;
                }
                self.end_array()
            }
            PeekedValue::PeekedObject => {
                self.begin_object()?;
                while self.has_next()? {
                    self.skip_name()?;
                    self.skip_value()?;
                }
                self.end_object()
            }
            _ => {
                self.peeked_value.take();
                Ok(())
            }
        }
    }

    fn skip_to_top_level(&mut self) -> Result<(), ReaderError> {
        unimplemented!()
    }

    fn transfer_to<W: JsonWriter>(&mut self, _json_writer: &mut W) -> Result<(), TransferError> {
        unimplemented!()
    }

    fn consume_trailing_whitespace(self) -> Result<(), ReaderError> {
        if self.reached_eof {
            Ok(())
        } else {
            self.delegate.consume_trailing_whitespace()
        }
    }

    fn current_position(&self, _include_path: bool) -> JsonReaderPosition {
        if self.peeked_name.is_some() {
            self.peeked_name_pos.clone().unwrap()
        } else if self.peeked_value.is_some() {
            self.peeked_value_pos.clone().unwrap()
        } else {
            // Use stored position instead of directly obtaining position from delegate
            // since its position might already be at the end of the partial JSON data,
            // even though the trailing JSON value is incomplete and won't be returned
            // by this reader
            self.after_peeked_pos.clone()
        }
    }
}

macro_rules! deserialize_partial {
    ($reader:expr, |$deserializer:ident| $deserializing_function:expr) => {{
        let delegate = JsonStreamReader::new($reader);
        let mut json_reader = PartialJsonReader::new(delegate);
        let mut d = JsonReaderDeserializer::new(&mut json_reader);
        let $deserializer = &mut d;
        $deserializing_function
    }};
}

#[test]
fn test() {
    #[derive(Debug, Deserialize, Clone, PartialEq)]
    #[serde(default)]
    struct Outer {
        a: u32,
        b: bool,
        c: Option<u32>,
        d: Vec<Inner>,
    }
    impl Default for Outer {
        fn default() -> Self {
            Self {
                a: Default::default(),
                b: Default::default(),
                c: Some(1), // Use something other than `None` to test JSON null handling
                d: Default::default(),
            }
        }
    }

    #[derive(Debug, Default, Deserialize, Clone, PartialEq)]
    #[serde(default)]
    struct Inner {
        e: String,
        f: f32,
    }

    let full_json = r#"{"a":2,"b":true,"c":null,"d":[{"e":"str\"","f":1.2e3}]}"#;
    let mut json = String::new();
    let mut outer = Outer::default();

    // Test handling of empty JSON
    let result = deserialize_partial!("".as_bytes(), |d| Outer::deserialize_in_place(
        d, &mut outer
    ));
    match result {
        Err(DeserializerError::ReaderError(ReaderError::SyntaxError(JsonSyntaxError {
            kind: SyntaxErrorKind::IncompleteDocument,
            ..
        }))) => {}
        r => panic!("Unexpected result: {r:?}"),
    }

    let mut expected_deserialized = Vec::<Outer>::new();
    expected_deserialized.extend_from_slice(&vec![Outer::default(); 7]);
    expected_deserialized.extend_from_slice(&vec![
        Outer {
            a: 2,
            ..Default::default()
        };
        7
    ]);
    expected_deserialized.extend_from_slice(&vec![
        Outer {
            a: 2,
            b: true,
            ..Default::default()
        };
        9
    ]);
    expected_deserialized.extend_from_slice(&vec![
        Outer {
            a: 2,
            b: true,
            c: None,
            ..Default::default()
        };
        7
    ]);
    expected_deserialized.extend_from_slice(&vec![
        Outer {
            a: 2,
            b: true,
            c: None,
            d: vec![Inner::default()]
        };
        11
    ]);
    expected_deserialized.extend_from_slice(&vec![
        Outer {
            a: 2,
            b: true,
            c: None,
            d: vec![Inner {
                e: "str\"".to_owned(),
                ..Default::default()
            }]
        };
        11
    ]);
    expected_deserialized.extend_from_slice(&vec![
        Outer {
            a: 2,
            b: true,
            c: None,
            d: vec![Inner {
                e: "str\"".to_owned(),
                f: 1.2e3
            }]
        };
        3
    ]);
    // Verify that test is properly implemented and number of expected values is equal to chars
    assert_eq!(full_json.chars().count(), expected_deserialized.len());

    for (index, c) in full_json.char_indices() {
        json.push(c);
        deserialize_partial!(json.as_bytes(), |d| Outer::deserialize_in_place(
            d, &mut outer
        ))
        .unwrap();
        assert_eq!(
            expected_deserialized[index], outer,
            "For char index {index}, JSON: {json}"
        );
    }
}

#[test]
fn unexpected_value() -> Result<(), Box<dyn std::error::Error>> {
    let json = "true";
    let mut json_reader = PartialJsonReader::new(JsonStreamReader::new(json.as_bytes()));
    match json_reader.next_number_as_str() {
        Err(ReaderError::UnexpectedValueType {
            expected: ValueType::Number,
            actual: ValueType::Boolean,
            location,
        }) => {
            assert_eq!(
                JsonReaderPosition {
                    path: None,
                    line_pos: Some(LinePosition { line: 0, column: 0 }),
                    data_pos: Some(0)
                },
                location
            );
        }
        r => panic!("unexpected result: {r:?}"),
    }
    assert_eq!(true, json_reader.next_bool()?);

    let json = "true";
    let mut json_reader = PartialJsonReader::new(JsonStreamReader::new(json.as_bytes()));
    match json_reader.begin_array() {
        Err(ReaderError::UnexpectedValueType {
            expected: ValueType::Array,
            actual: ValueType::Boolean,
            location,
        }) => {
            assert_eq!(
                JsonReaderPosition {
                    path: None,
                    line_pos: Some(LinePosition { line: 0, column: 0 }),
                    data_pos: Some(0)
                },
                location
            );
        }
        r => panic!("unexpected result: {r:?}"),
    }
    assert_eq!(true, json_reader.next_bool()?);

    let json = "[true]";
    let mut json_reader = PartialJsonReader::new(JsonStreamReader::new(json.as_bytes()));
    match json_reader.next_number_as_str() {
        Err(ReaderError::UnexpectedValueType {
            expected: ValueType::Number,
            actual: ValueType::Array,
            location,
        }) => {
            assert_eq!(
                JsonReaderPosition {
                    path: None,
                    line_pos: Some(LinePosition { line: 0, column: 0 }),
                    data_pos: Some(0)
                },
                location
            );
        }
        r => panic!("unexpected result: {r:?}"),
    }
    json_reader.begin_array()?;
    assert_eq!(true, json_reader.next_bool()?);
    json_reader.end_array()?;

    Ok(())
}

#[test]
fn end_incomplete() -> Result<(), Box<dyn std::error::Error>> {
    let json = "[";
    let mut json_reader = PartialJsonReader::new(JsonStreamReader::new(json.as_bytes()));
    json_reader.begin_array()?;
    // Directly calls `end_array()` without preceding `has_next()`
    json_reader.end_array()?;
    json_reader.consume_trailing_whitespace()?;

    let json = "{";
    let mut json_reader = PartialJsonReader::new(JsonStreamReader::new(json.as_bytes()));
    json_reader.begin_object()?;
    // Directly calls `end_object()` without preceding `has_next()`
    json_reader.end_object()?;
    json_reader.consume_trailing_whitespace()?;

    Ok(())
}

#[test]
fn unexpected_structure() -> Result<(), Box<dyn std::error::Error>> {
    let json = "[]";
    let mut json_reader = PartialJsonReader::new(JsonStreamReader::new(json.as_bytes()));
    json_reader.begin_array()?;
    match json_reader.peek() {
        Err(ReaderError::UnexpectedStructure {
            kind: UnexpectedStructureKind::FewerElementsThanExpected,
            location,
        }) => {
            assert_eq!(
                JsonReaderPosition {
                    path: None,
                    line_pos: Some(LinePosition { line: 0, column: 1 }),
                    data_pos: Some(1)
                },
                location
            );
        }
        r => panic!("unexpected result: {r:?}"),
    }
    json_reader.end_array()?;

    let json = "[true]";
    let mut json_reader = PartialJsonReader::new(JsonStreamReader::new(json.as_bytes()));
    json_reader.begin_array()?;
    match json_reader.end_array() {
        Err(ReaderError::UnexpectedStructure {
            kind: UnexpectedStructureKind::MoreElementsThanExpected,
            location,
        }) => {
            assert_eq!(
                JsonReaderPosition {
                    path: None,
                    line_pos: Some(LinePosition { line: 0, column: 1 }),
                    data_pos: Some(1)
                },
                location
            );
        }
        r => panic!("unexpected result: {r:?}"),
    }
    assert_eq!(true, json_reader.next_bool()?);
    json_reader.end_array()?;

    let json = "{}";
    let mut json_reader = PartialJsonReader::new(JsonStreamReader::new(json.as_bytes()));
    json_reader.begin_object()?;
    match json_reader.next_name() {
        Err(ReaderError::UnexpectedStructure {
            kind: UnexpectedStructureKind::FewerElementsThanExpected,
            location,
        }) => {
            assert_eq!(
                JsonReaderPosition {
                    path: None,
                    line_pos: Some(LinePosition { line: 0, column: 1 }),
                    data_pos: Some(1)
                },
                location
            );
        }
        r => panic!("unexpected result: {r:?}"),
    }
    json_reader.end_object()?;

    let json = "{\"a\": true}";
    let mut json_reader = PartialJsonReader::new(JsonStreamReader::new(json.as_bytes()));
    json_reader.begin_object()?;
    match json_reader.end_object() {
        Err(ReaderError::UnexpectedStructure {
            kind: UnexpectedStructureKind::MoreElementsThanExpected,
            location,
        }) => {
            assert_eq!(
                JsonReaderPosition {
                    path: None,
                    line_pos: Some(LinePosition { line: 0, column: 1 }),
                    data_pos: Some(1)
                },
                location
            );
        }
        r => panic!("unexpected result: {r:?}"),
    }
    assert_eq!("a", json_reader.next_name()?);
    assert_eq!(true, json_reader.next_bool()?);
    json_reader.end_object()?;

    Ok(())
}

#[test]
fn current_position() -> Result<(), Box<dyn std::error::Error>> {
    let json = r#" [ 1 , { "a" : [] , "b" : "#;
    let mut json_reader = PartialJsonReader::new(JsonStreamReader::new(json.as_bytes()));

    fn assert_pos(json_reader: &PartialJsonReader<impl JsonReader>, expected_column: u64) {
        let position = json_reader.current_position(true);
        assert_eq!(
            JsonReaderPosition {
                path: None,
                line_pos: Some(LinePosition {
                    line: 0,
                    column: expected_column,
                }),
                // Assume input is ASCII only on single line; treat column as byte pos
                data_pos: Some(expected_column)
            },
            position
        );
    }

    assert_pos(&json_reader, 0);
    assert_eq!(ValueType::Array, json_reader.peek()?);
    assert_pos(&json_reader, 1);
    json_reader.begin_array()?;
    assert_pos(&json_reader, 2);
    assert!(json_reader.has_next()?);
    assert_pos(&json_reader, 3);
    assert_eq!("1", json_reader.next_number_as_str()?);
    assert_pos(&json_reader, 7);
    assert!(json_reader.has_next()?);
    assert_pos(&json_reader, 7);
    json_reader.begin_object()?;
    assert_pos(&json_reader, 8);
    assert!(json_reader.has_next()?);
    assert_pos(&json_reader, 9);
    assert_eq!("a", json_reader.next_name()?);
    assert_pos(&json_reader, 15);
    assert_eq!(ValueType::Array, json_reader.peek()?);
    assert_pos(&json_reader, 15);
    json_reader.begin_array()?;
    assert_pos(&json_reader, 16);
    assert!(!json_reader.has_next()?);
    assert_pos(&json_reader, 16);
    json_reader.end_array()?;
    assert_pos(&json_reader, 17);
    // Here the end of valid JSON is reached
    assert!(!json_reader.has_next()?);
    assert_pos(&json_reader, 17);
    json_reader.end_object()?;
    assert_pos(&json_reader, 17);
    assert!(!json_reader.has_next()?);
    assert_pos(&json_reader, 17);
    json_reader.end_array()?;
    assert_pos(&json_reader, 17);

    Ok(())
}
