#![cfg(feature = "experimental")]
#![cfg(feature = "serde")]

use std::{error::Error, fmt::Debug};

use struson::{
    json_path,
    reader::{
        simple::{SimpleJsonReader, ValueReader},
        JsonStreamReader, ValueType,
    },
};

fn new_reader(json: &str) -> SimpleJsonReader<JsonStreamReader<&[u8]>> {
    SimpleJsonReader::new(json.as_bytes())
}

#[test]
fn read() -> Result<(), Box<dyn Error>> {
    let mut json_reader = new_reader("null");
    assert_eq!(ValueType::Null, json_reader.peek()?);
    json_reader.next_null()?;

    let json_reader = new_reader("true");
    assert_eq!(true, json_reader.next_bool()?);

    let json_reader = new_reader("\"test\"");
    assert_eq!("test", json_reader.next_string()?);

    let json_reader = new_reader("1");
    assert_eq!(1_u64, json_reader.next_number()??);

    let json_reader = new_reader("2.3");
    assert_eq!(2.3_f64, json_reader.next_number()??);

    let json_reader = new_reader("4.5e6");
    assert_eq!("4.5e6", json_reader.next_number_as_string()?);

    let json_reader = new_reader("\"serde\"");
    assert_eq!("serde", json_reader.deserialize_next::<String>()?);

    Ok(())
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
            {"nested": true}
        ]
        "#,
    );

    // Verify that result of closure is returned by method (value is arbitrary)
    let expected_return_value = 3;
    let return_value = json_reader.next_array(|mut array_reader| {
        assert!(array_reader.has_next()?);
        assert_eq!(ValueType::Null, array_reader.peek()?);

        array_reader.next_null()?;
        assert_eq!(true, array_reader.next_bool()?);
        assert_eq!("test", array_reader.next_string()?);
        assert_eq!(1_u64, array_reader.next_number()??);
        assert_eq!(2.3_f64, array_reader.next_number()??);
        assert_eq!("4.5e6", array_reader.next_number_as_string()?);
        assert_eq!("serde", array_reader.deserialize_next::<String>()?);

        array_reader.next_array(|array_reader| {
            assert_eq!(false, array_reader.next_bool()?);
            Ok(())
        })?;

        array_reader.next_object(|name, value_reader| {
            assert_eq!("nested", name);
            assert_eq!(true, value_reader.next_bool()?);
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
    json_reader.next_array_items(|item_reader| {
        values.push(item_reader.next_number()??);
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
    json_reader.next_array_items(|mut item_reader| {
        if item_reader.peek()? == ValueType::Number {
            let value = item_reader.next_number()??;
            values.push(value);
        }
        // Ignore other value types; don't consume the value

        Ok(())
    })?;
    assert_eq!(vec![1, 2, 3], values);
    Ok(())
}

#[test]
fn read_object() -> Result<(), Box<dyn Error>> {
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
            "i": {"nested": true}
        }
        "#,
    );

    let mut index = 0;
    json_reader.next_object(|name, value_reader| {
        let expected_name = char::from_u32(('a' as u32) + index).unwrap().to_string();
        assert_eq!(expected_name, name);

        match index {
            0 => value_reader.next_null()?,
            1 => assert_eq!(true, value_reader.next_bool()?),
            2 => assert_eq!("test", value_reader.next_string()?),
            3 => assert_eq!(1_u64, value_reader.next_number()??),
            4 => assert_eq!(2.3_f64, value_reader.next_number()??),
            5 => assert_eq!("4.5e6", value_reader.next_number_as_string()?),
            6 => assert_eq!("serde", value_reader.deserialize_next::<String>()?),
            7 => value_reader.next_array(|array_reader| {
                assert_eq!(false, array_reader.next_bool()?);
                Ok(())
            })?,
            8 => value_reader.next_object(|name, value_reader| {
                assert_eq!("nested", name);
                assert_eq!(true, value_reader.next_bool()?);
                Ok(())
            })?,
            _ => panic!("unexpected name '{name}' at index {index}"),
        };
        index += 1;
        Ok(())
    })?;
    assert_eq!(9, index);
    Ok(())
}

/// Tests the behavior when an object member value is not explicitly consumed
#[test]
fn object_member_value_not_consumed() -> Result<(), Box<dyn Error>> {
    let json_reader = new_reader(r#"{"a":1, "b": 2}"#);

    // Verify that closure was called
    let mut seen_second_member = false;
    json_reader.next_object(|name, value_reader| {
        match name.as_str() {
            "a" => {
                // Does not consume the value
            }
            "b" => {
                assert_eq!("2", value_reader.next_number_as_string()?);
                seen_second_member = true;
            }
            _ => panic!("unexpected member: {name}"),
        }

        Ok(())
    })?;

    assert!(seen_second_member);
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
    assert_eq!("2", json_reader.next_number_as_string()?);
    Ok(())
}

#[test]
fn skip() -> Result<(), Box<dyn Error>> {
    let json_reader = new_reader("true");
    json_reader.skip_next()?;

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
    json_reader.next_array(|array_reader| {
        array_reader.skip_next()?;
        array_reader.next_array_items(|array_reader| {
            array_reader.skip_next()?;
            Ok(())
        })?;

        array_reader.next_object(|name, value_reader| {
            match name.as_str() {
                "a" => value_reader.skip_next()?,
                "b" => {
                    assert_eq!("4", value_reader.next_number_as_string()?);
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
        json_reader.next_bool().map_err(|e| e.into()),
        "syntax error: JSON syntax error MalformedJson at path '$', line 0, column 0 (data pos 0)",
    );

    let json_reader = new_reader("1");
    assert_error(
        json_reader.next_bool().map_err(|e| e.into()),
        "expected JSON value type Boolean but got Number at path '$', line 0, column 0 (data pos 0)"
    );

    let json_reader = new_reader("[]");
    assert_error(
        json_reader.next_array(|array_reader| {
            array_reader.next_bool()?;
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

    // --- next_array ---
    let json_reader = new_reader("[");
    assert_error(json_reader.next_array(|_| Err(message.into())));

    let json_reader = new_reader("[[");
    assert_error(
        json_reader.next_array(|array_reader| array_reader.next_array(|_| Err(message.into()))),
    );

    let json_reader = new_reader("[{\"a\": 1");
    assert_error(
        json_reader.next_array(|array_reader| array_reader.next_object(|_, _| Err(message.into()))),
    );

    // --- next_array_items ---
    let json_reader = new_reader("[1");
    assert_error(json_reader.next_array_items(|_| Err(message.into())));

    let json_reader = new_reader("[[1");
    assert_error(
        json_reader.next_array_items(|item_reader| item_reader.next_array(|_| Err(message.into()))),
    );

    let json_reader = new_reader("[{\"a\": 1");
    assert_error(
        json_reader
            .next_array_items(|item_reader| item_reader.next_object(|_, _| Err(message.into()))),
    );

    // --- next_object ---
    let json_reader = new_reader("{\"a\": 1");
    assert_error(json_reader.next_object(|_, _| Err(message.into())));

    let json_reader = new_reader("{\"a\": [");
    assert_error(
        json_reader
            .next_object(|_name, value_reader| value_reader.next_array(|_| Err(message.into()))),
    );

    let json_reader = new_reader("{\"a\": {\"b\": 1");
    assert_error(
        json_reader.next_object(|_name, value_reader| {
            value_reader.next_object(|_, _| Err(message.into()))
        }),
    );
}
