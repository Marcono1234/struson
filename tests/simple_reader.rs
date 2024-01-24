//! Tests for [`struson::reader::simple`]

#![cfg(feature = "experimental")]
#![cfg(feature = "serde")]

use std::{error::Error, fmt::Debug};

use struson::{
    json_path,
    reader::{
        simple::{SimpleJsonReader, ValueReader},
        JsonStreamReader, JsonSyntaxError, ReaderError, SyntaxErrorKind, ValueType,
    },
};

fn new_reader(json: &str) -> SimpleJsonReader<JsonStreamReader<&[u8]>> {
    SimpleJsonReader::new(json.as_bytes())
}

#[test]
fn read() -> Result<(), Box<dyn Error>> {
    let mut json_reader = new_reader("null");
    assert_eq!(ValueType::Null, json_reader.peek_value()?);
    json_reader.read_null()?;

    let json_reader = new_reader("true");
    assert_eq!(true, json_reader.read_bool()?);

    let json_reader = new_reader("\"test\"");
    assert_eq!("test", json_reader.read_string()?);

    let json_reader = new_reader("1");
    assert_eq!(1_u64, json_reader.read_number()??);

    let json_reader = new_reader("2.3");
    assert_eq!(2.3_f64, json_reader.read_number()??);

    let json_reader = new_reader("4.5e6");
    assert_eq!("4.5e6", json_reader.read_number_as_string()?);

    let json_reader = new_reader("\"serde\"");
    assert_eq!("serde", json_reader.read_deserialize::<String>()?);

    Ok(())
}

/// Reading top-level value should also verify that there is no trailing data
#[test]
fn read_trailing_data() {
    let json_reader = new_reader("true 1");
    match json_reader.read_bool() {
        Err(ReaderError::SyntaxError(JsonSyntaxError {
            kind: SyntaxErrorKind::TrailingData,
            ..
        })) => {}
        r => panic!("unexpected result: {r:?}"),
    }
}

#[test]
fn read_array() -> Result<(), Box<dyn Error>> {
    let json_reader = new_reader(
        r#"
        [
            null,
            true,
            "test",
            1,
            2.3,
            4.5e6,
            "serde",
            [false],
            {"nested1": true},
            {"nested2": true}
        ]
        "#,
    );

    // Verify that result of closure is returned by method (value is arbitrary)
    let expected_return_value = 3;
    let return_value = json_reader.read_array(|mut array_reader| {
        assert!(array_reader.has_next()?);
        assert_eq!(ValueType::Null, array_reader.peek_value()?);

        array_reader.read_null()?;
        assert_eq!(true, array_reader.read_bool()?);
        assert_eq!("test", array_reader.read_string()?);
        assert_eq!(1_u64, array_reader.read_number()??);
        assert_eq!(2.3_f64, array_reader.read_number()??);
        assert_eq!("4.5e6", array_reader.read_number_as_string()?);
        assert_eq!("serde", array_reader.read_deserialize::<String>()?);

        array_reader.read_array(|array_reader| {
            assert_eq!(false, array_reader.read_bool()?);
            Ok(())
        })?;

        array_reader.read_object_borrowed_names(|mut member_reader| {
            assert_eq!("nested1", member_reader.read_name()?);
            assert_eq!(true, member_reader.read_bool()?);
            Ok(())
        })?;

        array_reader.read_object_owned_names(|name, value_reader| {
            assert_eq!("nested2", name);
            assert_eq!(true, value_reader.read_bool()?);
            Ok(())
        })?;

        assert!(!array_reader.has_next()?);

        Ok(expected_return_value)
    })?;
    assert_eq!(expected_return_value, return_value);
    Ok(())
}

#[test]
fn read_array_all() -> Result<(), Box<dyn Error>> {
    let json_reader = new_reader("[1, 2, 3]");
    let mut values = Vec::<u64>::new();
    let mut index = 0;
    json_reader.read_array_items(|mut item_reader| {
        if index == 1 {
            // Should also work properly when peeking before reading
            assert_eq!(ValueType::Number, item_reader.peek_value()?);
        }
        values.push(item_reader.read_number()??);
        index += 1;
        Ok(())
    })?;
    assert_eq!(vec![1, 2, 3], values);
    Ok(())
}

/// Tests the behavior when an array item is not explicitly consumed
#[test]
fn array_item_not_consumed() -> Result<(), Box<dyn Error>> {
    let json_reader = new_reader("[true, 1, 2, null, [], 3]");
    let mut values = Vec::<u64>::new();
    json_reader.read_array_items(|mut item_reader| {
        if item_reader.peek_value()? == ValueType::Number {
            let value = item_reader.read_number()??;
            values.push(value);
        }
        // Ignore other value types; don't consume the value

        Ok(())
    })?;
    assert_eq!(vec![1, 2, 3], values);
    Ok(())
}

#[test]
fn read_object_borrowed_names() -> Result<(), Box<dyn Error>> {
    let json_reader = new_reader(
        r#"
        {
            "a": null,
            "b": true,
            "c": "test",
            "d": 1,
            "e": 2.3,
            "f": 4.5e6,
            "g": "serde",
            "h": [false],
            "i": {"nested1": true},
            "j": {"nested2": true}
        }
        "#,
    );

    let mut index = 0;
    json_reader.read_object_borrowed_names(|mut member_reader| {
        let expected_name = char::from_u32(('a' as u32) + index).unwrap().to_string();
        let name = member_reader.read_name()?;
        assert_eq!(expected_name, name);

        match index {
            0 => member_reader.read_null()?,
            1 => {
                assert_eq!(ValueType::Boolean, member_reader.peek_value()?);
                assert_eq!(true, member_reader.read_bool()?);
            }
            2 => assert_eq!("test", member_reader.read_string()?),
            3 => assert_eq!(1_u64, member_reader.read_number()??),
            4 => assert_eq!(2.3_f64, member_reader.read_number()??),
            5 => assert_eq!("4.5e6", member_reader.read_number_as_string()?),
            6 => assert_eq!("serde", member_reader.read_deserialize::<String>()?),
            7 => member_reader.read_array(|array_reader| {
                assert_eq!(false, array_reader.read_bool()?);
                Ok(())
            })?,
            8 => member_reader.read_object_borrowed_names(|mut member_reader| {
                assert_eq!("nested1", member_reader.read_name()?);
                assert_eq!(true, member_reader.read_bool()?);
                Ok(())
            })?,
            9 => member_reader.read_object_owned_names(|name, value_reader| {
                assert_eq!("nested2", name);
                assert_eq!(true, value_reader.read_bool()?);
                Ok(())
            })?,
            _ => panic!("unexpected name '{name}' at index {index}"),
        };
        index += 1;
        Ok(())
    })?;
    assert_eq!(10, index);
    Ok(())
}

#[test]
fn read_object_owned_names() -> Result<(), Box<dyn Error>> {
    let json_reader = new_reader(
        r#"
        {
            "a": null,
            "b": true,
            "c": "test",
            "d": 1,
            "e": 2.3,
            "f": 4.5e6,
            "g": "serde",
            "h": [false],
            "i": {"nested1": true},
            "j": {"nested2": true}
        }
        "#,
    );

    let mut index = 0;
    json_reader.read_object_owned_names(|name, mut value_reader| {
        let expected_name = char::from_u32(('a' as u32) + index).unwrap().to_string();
        assert_eq!(expected_name, name);

        match index {
            0 => value_reader.read_null()?,
            1 => {
                assert_eq!(ValueType::Boolean, value_reader.peek_value()?);
                assert_eq!(true, value_reader.read_bool()?);
            }
            2 => assert_eq!("test", value_reader.read_string()?),
            3 => assert_eq!(1_u64, value_reader.read_number()??),
            4 => assert_eq!(2.3_f64, value_reader.read_number()??),
            5 => assert_eq!("4.5e6", value_reader.read_number_as_string()?),
            6 => assert_eq!("serde", value_reader.read_deserialize::<String>()?),
            7 => value_reader.read_array(|array_reader| {
                assert_eq!(false, array_reader.read_bool()?);
                Ok(())
            })?,
            8 => value_reader.read_object_borrowed_names(|mut member_reader| {
                assert_eq!("nested1", member_reader.read_name()?);
                assert_eq!(true, member_reader.read_bool()?);
                Ok(())
            })?,
            9 => value_reader.read_object_owned_names(|name, value_reader| {
                assert_eq!("nested2", name);
                assert_eq!(true, value_reader.read_bool()?);
                Ok(())
            })?,
            _ => panic!("unexpected name '{name}' at index {index}"),
        };
        index += 1;
        Ok(())
    })?;
    assert_eq!(10, index);
    Ok(())
}

/// Tests the behavior when for [`ValueReader::read_object_borrowed_names`] the name or value
/// of an object member value is not explicitly consumed
#[test]
fn object_borrowed_member_not_consumed() -> Result<(), Box<dyn Error>> {
    let json_reader = new_reader(r#"{"a":1, "b": 2, "c": 3, "d": 4, "e": 5}"#);

    let mut index = 0;
    json_reader.read_object_borrowed_names(|mut member_reader| {
        match index {
            0 => {
                // Skip both name and value
            }
            1 => {
                // Skip name

                assert_eq!("2", member_reader.read_number_as_string()?);
            }
            2 => {
                // Skip name by peeking at value; and don't consume value
                assert_eq!(ValueType::Number, member_reader.peek_value()?);
            }
            3 => {
                // Peeking twice and then reading should only try to skip name once
                assert_eq!(ValueType::Number, member_reader.peek_value()?);
                assert_eq!(ValueType::Number, member_reader.peek_value()?);
                assert_eq!("4", member_reader.read_number_as_string()?);
            }
            _ => {
                assert_eq!("e", member_reader.read_name()?);
                assert_eq!("5", member_reader.read_number_as_string()?);
            }
        }

        index += 1;
        Ok(())
    })?;
    assert_eq!(5, index);
    Ok(())
}

#[test]
#[should_panic(expected = "name has already been consumed")]
fn object_borrowed_name_read_twice() {
    let json_reader = new_reader(r#"{"a":1}"#);
    json_reader
        .read_object_borrowed_names(|mut member_reader| {
            member_reader.read_name()?;
            member_reader.read_name()?;
            Ok(())
        })
        .unwrap();
}

/// Tests the behavior when for [`ValueReader::read_object_owned_names`] an object
/// member value is not explicitly consumed
#[test]
fn object_owned_member_value_not_consumed() -> Result<(), Box<dyn Error>> {
    let json_reader = new_reader(r#"{"a":1, "b": 2, "c": 3}"#);

    // Verify that closure was called
    let mut seen_last_member = false;
    json_reader.read_object_owned_names(|name, mut value_reader| {
        match name.as_str() {
            "a" => {
                // Does not consume the value
            }
            "b" => {
                // Peek at value but don't consume it
                assert_eq!(ValueType::Number, value_reader.peek_value()?);
            }
            "c" => {
                assert_eq!("3", value_reader.read_number_as_string()?);
                seen_last_member = true;
            }
            _ => panic!("unexpected member: {name}"),
        }

        Ok(())
    })?;

    assert!(seen_last_member);
    Ok(())
}

#[test]
fn seek_to() -> Result<(), Box<dyn Error>> {
    let mut json_reader = new_reader(
        r#"
        [
            null,
            true,
            {
                "a": 1,
                "b": 2
            }
        ]
        "#,
    );

    json_reader.seek_to(&json_path![2, "b"])?;
    assert_eq!("2", json_reader.read_number_as_string()?);

    let mut json_reader = new_reader("[1, [2, 3]]");
    json_reader.seek_to(&json_path![1])?;
    // Should support seeking multiple times
    json_reader.seek_to(&json_path![0])?;
    assert_eq!("2", json_reader.read_number_as_string()?);
    Ok(())
}

#[test]
fn skip() -> Result<(), Box<dyn Error>> {
    let json_reader = new_reader("true");
    json_reader.skip_value()?;

    let json_reader = new_reader(
        r#"
        [
            null,
            [1, 2],
            {
                "a": 3,
                "b": 4
            }
        ]
        "#,
    );

    // Verify that closure was actually called
    let mut found_value = false;
    json_reader.read_array(|array_reader| {
        array_reader.skip_value()?;
        array_reader.read_array_items(|array_reader| {
            array_reader.skip_value()?;
            Ok(())
        })?;

        array_reader.read_object_owned_names(|name, value_reader| {
            match name.as_str() {
                "a" => value_reader.skip_value()?,
                "b" => {
                    assert_eq!("4", value_reader.read_number_as_string()?);
                    found_value = true;
                }
                _ => panic!("unexpected name: {name}"),
            };
            Ok(())
        })
    })?;
    assert!(found_value);

    Ok(())
}

#[test]
fn errors() {
    fn assert_error<T: Debug>(result: Result<T, Box<dyn Error>>, expected_message: &str) {
        match result {
            Err(e) => assert_eq!(expected_message, e.to_string()),
            _ => panic!("unexpected result: {result:?}"),
        }
    }

    let json_reader = new_reader("?");
    assert_error(
        json_reader.read_bool().map_err(|e| e.into()),
        "syntax error: JSON syntax error MalformedJson at path '$', line 0, column 0 (data pos 0)",
    );

    let json_reader = new_reader("1");
    assert_error(
        json_reader.read_bool().map_err(|e| e.into()),
        "expected JSON value type Boolean but got Number at path '$', line 0, column 0 (data pos 0)"
    );

    let json_reader = new_reader("[]");
    assert_error(
        json_reader.read_array(|array_reader| {
            array_reader.read_bool()?;
            Ok(())
        }),
        "unexpected JSON structure FewerElementsThanExpected at path '$[0]', line 0, column 1 (data pos 1)",
    );
}

/// Verifies that errors returned by closures are propagated and abort processing
///
/// Especially after the closure returned an error no further `JsonReader` methods should be
/// called since that could cause a panic.
#[test]
fn closure_error_propagation() {
    let message = "custom-message";
    fn assert_error(result: Result<(), Box<dyn Error>>) {
        match result {
            Err(e) => assert_eq!("custom-message", e.to_string()),
            _ => panic!("unexpected result: {result:?}"),
        }
    }

    // --- read_array ---
    let json_reader = new_reader("[");
    assert_error(json_reader.read_array(|_| Err(message.into())));

    let json_reader = new_reader("[[");
    assert_error(
        json_reader.read_array(|array_reader| array_reader.read_array(|_| Err(message.into()))),
    );

    let json_reader = new_reader("[{\"a\": 1");
    assert_error(json_reader.read_array(|array_reader| {
        array_reader.read_object_borrowed_names(|_| Err(message.into()))
    }));

    let json_reader = new_reader("[{\"a\": 1");
    assert_error(json_reader.read_array(|array_reader| {
        array_reader.read_object_owned_names(|_, _| Err(message.into()))
    }));

    // --- read_array_items ---
    let json_reader = new_reader("[1");
    assert_error(json_reader.read_array_items(|_| Err(message.into())));

    let json_reader = new_reader("[[1");
    assert_error(
        json_reader.read_array_items(|item_reader| item_reader.read_array(|_| Err(message.into()))),
    );

    let json_reader = new_reader("[{\"a\": 1");
    assert_error(json_reader.read_array_items(|item_reader| {
        item_reader.read_object_borrowed_names(|_| Err(message.into()))
    }));

    let json_reader = new_reader("[{\"a\": 1");
    assert_error(json_reader.read_array_items(|item_reader| {
        item_reader.read_object_owned_names(|_, _| Err(message.into()))
    }));

    // --- read_object_borrowed_names ---
    let json_reader = new_reader("{\"a\": 1");
    assert_error(json_reader.read_object_borrowed_names(|_| Err(message.into())));

    let json_reader = new_reader("{\"a\": [");
    assert_error(json_reader.read_object_borrowed_names(|member_reader| {
        member_reader.read_array(|_| Err(message.into()))
    }));

    let json_reader = new_reader("{\"a\": {\"b\": 1");
    assert_error(json_reader.read_object_borrowed_names(|member_reader| {
        member_reader.read_object_borrowed_names(|_| Err(message.into()))
    }));

    let json_reader = new_reader("{\"a\": {\"b\": 1");
    assert_error(json_reader.read_object_borrowed_names(|member_reader| {
        member_reader.read_object_owned_names(|_, _| Err(message.into()))
    }));

    // --- read_object_owned_names ---
    let json_reader = new_reader("{\"a\": 1");
    assert_error(json_reader.read_object_owned_names(|_, _| Err(message.into())));

    let json_reader = new_reader("{\"a\": [");
    assert_error(json_reader.read_object_owned_names(|_name, value_reader| {
        value_reader.read_array(|_| Err(message.into()))
    }));

    let json_reader = new_reader("{\"a\": {\"b\": 1");
    assert_error(json_reader.read_object_owned_names(|_name, value_reader| {
        value_reader.read_object_borrowed_names(|_| Err(message.into()))
    }));

    let json_reader = new_reader("{\"a\": {\"b\": 1");
    assert_error(json_reader.read_object_owned_names(|_name, value_reader| {
        value_reader.read_object_owned_names(|_, _| Err(message.into()))
    }));
}
