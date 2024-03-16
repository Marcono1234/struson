//! Tests for [`struson::reader::simple`]

#![cfg(feature = "experimental")]
#![cfg(feature = "serde")]

use std::{
    cmp::min,
    error::Error,
    fmt::Debug,
    io::{ErrorKind, Read},
};

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
    assert_eq!("test", json_reader.read_str(|s| Ok(s.to_owned()))?);

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
fn read_string_with_reader() -> Result<(), Box<dyn Error>> {
    let json_reader = new_reader("\"\"");
    let value = json_reader.read_string_with_reader(|mut reader| {
        let mut buf = String::new();
        reader.read_to_string(&mut buf)?;
        Ok(buf)
    })?;
    assert_eq!("", value);

    let json_reader = new_reader("\"test\"");
    let value = json_reader.read_string_with_reader(|mut reader| {
        let mut buf = String::new();
        reader.read_to_string(&mut buf)?;
        Ok(buf)
    })?;
    assert_eq!("test", value);

    let json_reader = new_reader("\"test\"");
    let value = json_reader.read_string_with_reader(|mut reader| {
        let mut value = Vec::new();

        let mut buf = [0_u8; 1];
        while reader.read(&mut buf)? > 0 {
            value.push(buf[0]);
        }
        Ok(value)
    })?;
    assert_eq!(b"test" as &[u8], value);

    let json_reader = new_reader("[\"some string\", 12]");
    let value = json_reader.read_array(|array_reader| {
        let value = array_reader.read_string_with_reader(|mut reader| {
            let mut value = Vec::new();

            let mut buf = [0_u8; 1];
            let read_count = reader.read(&mut buf)?;
            assert_eq!(1, read_count);
            value.push(buf[0]);

            // Implicitly skip remainder

            Ok(value)
        })?;
        assert_eq!(b"s" as &[u8], value);

        Ok(array_reader.read_number_as_string()?)
    })?;
    assert_eq!("12", value);

    let json_reader = new_reader("1");
    // Verify closure is not called if value is not a string
    let result = json_reader.read_string_with_reader::<()>(|_| {
        panic!("should not have been called");
    });
    assert_eq!(
        "expected JSON value type String but got Number at path '$', line 0, column 0 (data pos 0)",
        result.unwrap_err().to_string()
    );

    Ok(())
}

#[test]
fn read_array() -> Result<(), Box<dyn Error>> {
    let json_reader = new_reader(
        r#"
        [
            null,
            true,
            "str",
            "string",
            "string-reader",
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
        assert_eq!("str", array_reader.read_str(|s| Ok(s.to_owned()))?);
        assert_eq!("string", array_reader.read_string()?);
        assert_eq!(
            "string-reader",
            array_reader.read_string_with_reader(|mut r| {
                let mut buf = String::new();
                r.read_to_string(&mut buf)?;
                Ok(buf)
            })?
        );
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
fn read_array_unexpected_items_count() {
    let json_reader = new_reader("[]");
    let result = json_reader.read_array(|array_reader| {
        array_reader.read_bool()?;
        Ok(())
    });
    assert_eq!(
        "unexpected JSON structure FewerElementsThanExpected at path '$[0]', line 0, column 1 (data pos 1)",
        result.unwrap_err().to_string()
    );

    let json_reader = new_reader("[1]");
    let result = json_reader.read_array(|_| {
        // Does not read any items
        Ok(())
    });
    assert_eq!(
        "unexpected JSON structure MoreElementsThanExpected at path '$[0]', line 0, column 1 (data pos 1)",
        result.unwrap_err().to_string()
    );
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
            "c": "str",
            "d": "string",
            "e": "string-reader",
            "f": 1,
            "g": 2.3,
            "h": 4.5e6,
            "i": "serde",
            "j": [false],
            "k": {"nested1": true},
            "l": {"nested2": true}
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
            2 => assert_eq!("str", member_reader.read_str(|s| Ok(s.to_owned()))?),
            3 => assert_eq!("string", member_reader.read_string()?),
            4 => assert_eq!(
                "string-reader",
                member_reader.read_string_with_reader(|mut r| {
                    let mut buf = String::new();
                    r.read_to_string(&mut buf)?;
                    Ok(buf)
                })?
            ),
            5 => assert_eq!(1_u64, member_reader.read_number()??),
            6 => assert_eq!(2.3_f64, member_reader.read_number()??),
            7 => assert_eq!("4.5e6", member_reader.read_number_as_string()?),
            8 => assert_eq!("serde", member_reader.read_deserialize::<String>()?),
            9 => member_reader.read_array(|array_reader| {
                assert_eq!(false, array_reader.read_bool()?);
                Ok(())
            })?,
            10 => member_reader.read_object_borrowed_names(|mut member_reader| {
                assert_eq!("nested1", member_reader.read_name()?);
                assert_eq!(true, member_reader.read_bool()?);
                Ok(())
            })?,
            11 => member_reader.read_object_owned_names(|name, value_reader| {
                assert_eq!("nested2", name);
                assert_eq!(true, value_reader.read_bool()?);
                Ok(())
            })?,
            _ => panic!("unexpected name '{name}' at index {index}"),
        };
        index += 1;
        Ok(())
    })?;
    assert_eq!(12, index);
    Ok(())
}

#[test]
fn read_object_owned_names() -> Result<(), Box<dyn Error>> {
    let json_reader = new_reader(
        r#"
        {
            "a": null,
            "b": true,
            "c": "str",
            "d": "string",
            "e": "string-reader",
            "f": 1,
            "g": 2.3,
            "h": 4.5e6,
            "i": "serde",
            "j": [false],
            "k": {"nested1": true},
            "l": {"nested2": true}
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
            2 => assert_eq!("str", value_reader.read_str(|s| Ok(s.to_owned()))?),
            3 => assert_eq!("string", value_reader.read_string()?),
            4 => assert_eq!(
                "string-reader",
                value_reader.read_string_with_reader(|mut r| {
                    let mut buf = String::new();
                    r.read_to_string(&mut buf)?;
                    Ok(buf)
                })?
            ),
            5 => assert_eq!(1_u64, value_reader.read_number()??),
            6 => assert_eq!(2.3_f64, value_reader.read_number()??),
            7 => assert_eq!("4.5e6", value_reader.read_number_as_string()?),
            8 => assert_eq!("serde", value_reader.read_deserialize::<String>()?),
            9 => value_reader.read_array(|array_reader| {
                assert_eq!(false, array_reader.read_bool()?);
                Ok(())
            })?,
            10 => value_reader.read_object_borrowed_names(|mut member_reader| {
                assert_eq!("nested1", member_reader.read_name()?);
                assert_eq!(true, member_reader.read_bool()?);
                Ok(())
            })?,
            11 => value_reader.read_object_owned_names(|name, value_reader| {
                assert_eq!("nested2", name);
                assert_eq!(true, value_reader.read_bool()?);
                Ok(())
            })?,
            _ => panic!("unexpected name '{name}' at index {index}"),
        };
        index += 1;
        Ok(())
    })?;
    assert_eq!(12, index);
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
fn read_seeked() -> Result<(), Box<dyn Error>> {
    // Empty path
    let json_reader = new_reader("true");
    let mut values = Vec::new();
    // Seeking empty path
    json_reader.read_seeked(&json_path![], |value_reader| {
        values.push(value_reader.read_bool()?);
        Ok(())
    })?;
    assert_eq!(vec![true], values);

    // Value not consumed (implicitly skipped)
    let json_reader = new_reader("true");
    let mut call_count = 0;
    // Seeking empty path
    json_reader.read_seeked(&json_path![], |_| {
        call_count += 1;
        Ok(())
    })?;
    assert_eq!(1, call_count);

    // Error: Empty JSON document and value not consumed
    let json_reader = new_reader("");
    // Seeking empty path
    let result = json_reader.read_seeked(&json_path![], |_| Ok(()));
    assert_eq!(
        "syntax error: JSON syntax error IncompleteDocument at path '$', line 0, column 0 (data pos 0)",
        result.unwrap_err().to_string()
    );

    // Returning result
    let json_reader = new_reader(r#"{"a": 1, "a": 2}"#);
    let result = json_reader.read_seeked(&json_path!["a"], |value_reader| {
        Ok(value_reader.read_number_as_string()?)
    })?;
    assert_eq!("1", result);

    // Duplicate member
    let json_reader = new_reader(r#"{"a": 1, "a": 2}"#);
    let mut values = Vec::new();
    json_reader.read_seeked(&json_path!["a"], |value_reader| {
        values.push(value_reader.read_number_as_string()?);
        Ok(())
    })?;
    assert_eq!(vec!["1"], values);

    // Error: Wrong JSON value type
    let json_reader = new_reader("[1]");
    // Seeking empty path
    let result = json_reader.read_seeked::<()>(&json_path!["a"], |_| {
        panic!("should not have been called");
    });
    assert_eq!(
        "expected JSON value type Object but got Array at path '$', line 0, column 0 (data pos 0)",
        result.unwrap_err().to_string()
    );

    // Mixed with `seek_to`
    let mut json_reader = new_reader(r#"{"a": 1, "b": [{"c": 2, "d": 3}]}"#);
    let mut values = Vec::new();
    json_reader.seek_to(&json_path!["b"])?;
    json_reader.read_seeked(&json_path![0, "c"], |value_reader| {
        values.push(value_reader.read_number_as_string()?);
        Ok(())
    })?;
    assert_eq!(vec!["2"], values);

    // Error propagation
    let json_reader = new_reader("[1]");
    let result = json_reader.read_seeked::<()>(&json_path![0], |_| Err("custom-error".into()));
    assert_eq!("custom-error", result.unwrap_err().to_string());

    // Nested usage inside of other reading methods, including nested inside another `read_seeked` call
    let json_reader = new_reader(
        r#"
        [
            "item-1",
            {
                "a": [
                    "nested",
                    [1, 2]
                ]
            },
            "item-3"
        ]
        "#,
    );
    let mut values = Vec::new();
    json_reader.read_array(|array_reader| {
        assert_eq!("item-1", array_reader.read_string()?);

        array_reader.read_seeked(&json_path!["a"], |value_reader| {
            value_reader.read_array(|array_reader| {
                assert_eq!("nested", array_reader.read_string()?);

                array_reader.read_seeked(&json_path![1], |value_reader| {
                    values.push(value_reader.read_number_as_string()?);
                    Ok(())
                })
            })
        })?;

        assert_eq!("item-3", array_reader.read_string()?);
        Ok(())
    })?;
    // Check this outside of closure to make sure closure was called
    assert_eq!(vec!["2"], values);

    Ok(())
}

/// Tests for [`ValueReader::read_seeked_multi`]
mod read_seeked_multi {
    use super::*;
    use struson::reader::simple::multi_json_path::multi_json_path;

    #[test]
    fn empty_path() -> Result<(), Box<dyn Error>> {
        let json_reader = new_reader("true");
        let mut values = Vec::new();
        // Seeking empty path
        json_reader.read_seeked_multi(&multi_json_path![], true, |value_reader| {
            values.push(value_reader.read_bool()?);
            Ok(())
        })?;
        assert_eq!(vec![true], values);

        // Value not consumed (implicitly skipped)
        let json_reader = new_reader("true");
        let mut call_count = 0;
        // Seeking empty path
        json_reader.read_seeked_multi(&multi_json_path![], true, |_| {
            call_count += 1;
            Ok(())
        })?;
        assert_eq!(1, call_count);

        // Error: Empty JSON document and value not consumed
        let json_reader = new_reader("");
        // Seeking empty path
        let result = json_reader.read_seeked_multi(&multi_json_path![], true, |_| Ok(()));
        assert_eq!(
            "syntax error: JSON syntax error IncompleteDocument at path '$', line 0, column 0 (data pos 0)",
            result.unwrap_err().to_string()
        );

        Ok(())
    }

    /// Tests handling of a 'plain' JSON path without any wildcards
    #[test]
    fn plain_path() -> Result<(), Box<dyn Error>> {
        let json_reader = new_reader(r#"{"a": true, "b": [1, 2, 3], "c": false}"#);
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path!["b", 1], true, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["2"], values);

        let json_reader = new_reader(r#"[true, {"a": 1, "b": 2, "c": 3}, false]"#);
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![1, "b"], true, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["2"], values);

        // Duplicate member
        let json_reader = new_reader(r#"{"a": 1, "a": 2}"#);
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path!["a"], true, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["1"], values);

        // Value not consumed (implicitly skipped)
        let json_reader = new_reader("[true]");
        let mut call_count = 0;
        json_reader.read_seeked_multi(&multi_json_path![0], true, |_| {
            call_count += 1;
            Ok(())
        })?;
        assert_eq!(1, call_count);

        // Error: No match (regardless of `at_least_one_match = false`)
        let json_reader = new_reader(r#"[true]"#);
        let result = json_reader.read_seeked_multi(&multi_json_path![1], false, |_| {
            panic!("should not have been called");
        });
        assert_eq!(
            "unexpected JSON structure TooShortArray(expected_index = 1) at path '$[1]', line 0, column 5 (data pos 5)",
            result.unwrap_err().to_string()
        );

        // Error: No match (regardless of `at_least_one_match = false`)
        let json_reader = new_reader(r#"{"a": 1}"#);
        let result = json_reader.read_seeked_multi(&multi_json_path!["b"], false, |_| {
            panic!("should not have been called");
        });
        assert_eq!(
            "unexpected JSON structure MissingObjectMember(\"b\") at path '$.a', line 0, column 7 (data pos 7)",
            result.unwrap_err().to_string()
        );

        // Error: Wrong JSON value type
        let json_reader = new_reader("{}");
        let result = json_reader.read_seeked_multi(&multi_json_path![1], true, |_| {
            panic!("should not have been called");
        });
        assert_eq!(
            "expected JSON value type Array but got Object at path '$', line 0, column 0 (data pos 0)",
            result.unwrap_err().to_string()
        );

        // Error: Wrong JSON value type
        let json_reader = new_reader("[]");
        let result = json_reader.read_seeked_multi(&multi_json_path!["a"], true, |_| {
            panic!("should not have been called");
        });
        assert_eq!(
            "expected JSON value type Object but got Array at path '$', line 0, column 0 (data pos 0)",
            result.unwrap_err().to_string()
        );

        Ok(())
    }

    /// Tests usage of `[*]` path
    #[test]
    fn all_array() -> Result<(), Box<dyn Error>> {
        let json_reader = new_reader("[1, 2, 3]");
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![[*]], true, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["1", "2", "3"], values);

        // Nested arrays empty; no error despite `at_least_one_match = true`
        let json_reader = new_reader("[[], [1, 2], [], [3]]");
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![[*], [*]], true, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["1", "2", "3"], values);

        // Values not consumed (implicitly skipped)
        let json_reader = new_reader("[true, false, null]");
        let mut call_count = 0;
        json_reader.read_seeked_multi(&multi_json_path![[*]], true, |_| {
            call_count += 1;
            Ok(())
        })?;
        assert_eq!(3, call_count);

        // No match
        let json_reader = new_reader("[]");
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![[*]], false, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(Vec::<String>::new(), values);

        // Error: No match
        let json_reader = new_reader("[]");
        let result = json_reader.read_seeked_multi(&multi_json_path![[*]], true, |_| {
            panic!("should not have been called");
        });
        assert_eq!(
            "no matching value found for path '[*]' at path '$', line 0, column 0 (data pos 0)",
            result.unwrap_err().to_string()
        );

        // Error: Wrong JSON value type
        let json_reader = new_reader("{}");
        let result = json_reader.read_seeked_multi(&multi_json_path![[*]], false, |_| {
            panic!("should not have been called");
        });
        assert_eq!(
            "expected JSON value type Array but got Object at path '$', line 0, column 0 (data pos 0)",
            result.unwrap_err().to_string()
        );

        Ok(())
    }

    /// Tests usage of `[+]` path
    #[test]
    fn all_array_non_empty() -> Result<(), Box<dyn Error>> {
        let json_reader = new_reader("[1, 2, 3]");
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![[+]], true, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["1", "2", "3"], values);

        // Values not consumed (implicitly skipped)
        let json_reader = new_reader("[true, false, null]");
        let mut call_count = 0;
        json_reader.read_seeked_multi(&multi_json_path![[+]], true, |_| {
            call_count += 1;
            Ok(())
        })?;
        assert_eq!(3, call_count);

        // Succeeds if `[+]` is nested and not reached
        let json_reader = new_reader("[]");
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![[*], [+]], false, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(Vec::<String>::new(), values);

        // Non-trailing `[+]`
        let json_reader = new_reader("[[1, 2], [3, 4]]");
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![[+], 0], false, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["1", "3"], values);

        // Error: Empty nested array
        let json_reader = new_reader("[[1], []]");
        let mut values = Vec::new();
        let result =
            json_reader.read_seeked_multi(&multi_json_path![[*], [+]], false, |value_reader| {
                values.push(value_reader.read_number_as_string()?);
                Ok(())
            });
        assert_eq!(
            "unexpected JSON structure FewerElementsThanExpected at path '$[1][0]', line 0, column 7 (data pos 7)",
            result.unwrap_err().to_string()
        );
        // Should have already collected the first value
        assert_eq!(vec!["1"], values);

        // Error: Empty array (regardless of `at_least_one_match = false`)
        let json_reader = new_reader("[]");
        let result = json_reader.read_seeked_multi(&multi_json_path![[+]], false, |_| {
            panic!("should not have been called");
        });
        assert_eq!(
            "unexpected JSON structure FewerElementsThanExpected at path '$[0]', line 0, column 1 (data pos 1)",
            result.unwrap_err().to_string()
        );

        // Error: No match for previous piece, with `at_least_one_match = true`
        // This is mainly to check the formatted path in the error message
        let json_reader = new_reader("[]");
        let result = json_reader.read_seeked_multi(&multi_json_path![[*], [+]], true, |_| {
            panic!("should not have been called");
        });
        assert_eq!(
            "no matching value found for path '[*][+]' at path '$', line 0, column 0 (data pos 0)",
            result.unwrap_err().to_string()
        );

        Ok(())
    }

    /// Tests usage of `{*}` path
    #[test]
    fn all_object() -> Result<(), Box<dyn Error>> {
        let json_reader = new_reader(r#"{"a": 1, "b": 2, "c": 3}"#);
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![{*}], true, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["1", "2", "3"], values);

        // Duplicate member
        let json_reader = new_reader(r#"{"a": 1, "a": 2}"#);
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![{*}], true, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["1", "2"], values);

        // Nested objects empty; no error despite `at_least_one_match = true`
        let json_reader = new_reader(r#"[{}, {"a": 1, "b": 2}, {}, {"c": 3}]"#);
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![[*], {*}], true, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["1", "2", "3"], values);

        // Values not consumed (implicitly skipped)
        let json_reader = new_reader(r#"{"a": 1, "a": 2}"#);
        let mut call_count = 0;
        json_reader.read_seeked_multi(&multi_json_path![{*}], true, |_| {
            call_count += 1;
            Ok(())
        })?;
        assert_eq!(2, call_count);

        // No match
        let json_reader = new_reader("{}");
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![{*}], false, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(Vec::<String>::new(), values);

        // Error: No match
        let json_reader = new_reader("{}");
        let result = json_reader.read_seeked_multi(&multi_json_path![{*}], true, |_| {
            panic!("should not have been called");
        });
        assert_eq!(
            "no matching value found for path '.*' at path '$', line 0, column 0 (data pos 0)",
            result.unwrap_err().to_string()
        );

        // Error: Wrong JSON value type
        let json_reader = new_reader("[]");
        let result = json_reader.read_seeked_multi(&multi_json_path![{*}], false, |_| {
            panic!("should not have been called");
        });
        assert_eq!(
            "expected JSON value type Object but got Array at path '$', line 0, column 0 (data pos 0)",
            result.unwrap_err().to_string()
        );

        Ok(())
    }

    /// Tests usage of `{+}` path
    #[test]
    fn all_object_non_empty() -> Result<(), Box<dyn Error>> {
        let json_reader = new_reader(r#"{"a": 1, "b": 2, "c": 3}"#);
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![{*}], true, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["1", "2", "3"], values);

        // Values not consumed (implicitly skipped)
        let json_reader = new_reader(r#"{"a": 1, "a": 2}"#);
        let mut call_count = 0;
        json_reader.read_seeked_multi(&multi_json_path![{+}], true, |_| {
            call_count += 1;
            Ok(())
        })?;
        assert_eq!(2, call_count);

        // Succeeds if `{+}` is nested and not reached
        let json_reader = new_reader(r#"{}"#);
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![{*}, {+}], false, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(Vec::<String>::new(), values);

        // Non-trailing `{+}`
        let json_reader = new_reader(r#"{"a": [1, 2], "b": [3, 4]}"#);
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![{+}, 0], false, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["1", "3"], values);

        // Error: Empty nested object
        let json_reader = new_reader(r#"[{"a": 1}, {}]"#);
        let mut values = Vec::new();
        let result =
            json_reader.read_seeked_multi(&multi_json_path![[*], {+}], false, |value_reader| {
                values.push(value_reader.read_number_as_string()?);
                Ok(())
            });
        assert_eq!(
            "unexpected JSON structure FewerElementsThanExpected at path '$[1].<?>', line 0, column 12 (data pos 12)",
            result.unwrap_err().to_string()
        );
        // Should have already collected the first value
        assert_eq!(vec!["1"], values);

        // Error: Empty object (regardless of `at_least_one_match = false`)
        let json_reader = new_reader("{}");
        let result = json_reader.read_seeked_multi(&multi_json_path![{+}], false, |_| {
            panic!("should not have been called");
        });
        assert_eq!(
            "unexpected JSON structure FewerElementsThanExpected at path '$.<?>', line 0, column 1 (data pos 1)",
            result.unwrap_err().to_string()
        );

        // Error: No match for previous piece, with `at_least_one_match = true`
        // This is mainly to check the formatted path in the error message
        let json_reader = new_reader("{}");
        let result = json_reader.read_seeked_multi(&multi_json_path![{*}, {+}], true, |_| {
            panic!("should not have been called");
        });
        assert_eq!(
            "no matching value found for path '.*.+' at path '$', line 0, column 0 (data pos 0)",
            result.unwrap_err().to_string()
        );

        Ok(())
    }

    /// Tests usage of `?name` path
    #[test]
    fn optional_member() -> Result<(), Box<dyn Error>> {
        let json_reader = new_reader(r#"{"a": 1, "b": 2, "c": 3}"#);
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![?"b"], true, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["2"], values);

        // Duplicate member
        let json_reader = new_reader(r#"{"a": 1, "a": 2}"#);
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![?"a"], true, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["1"], values);

        // Value not consumed (implicitly skipped)
        let json_reader = new_reader(r#"{"a": true, "b": false, "c": null}"#);
        let mut call_count = 0;
        json_reader.read_seeked_multi(&multi_json_path![?"b"], true, |_| {
            call_count += 1;
            Ok(())
        })?;
        assert_eq!(1, call_count);

        // No match
        let json_reader = new_reader("{}");
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![?"b"], false, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(Vec::<String>::new(), values);

        // No match
        let json_reader = new_reader(r#"{"a": 1, "b": 2}"#);
        let mut values = Vec::new();
        json_reader.read_seeked_multi(&multi_json_path![?"x"], false, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(Vec::<String>::new(), values);

        // Error: No match
        let json_reader = new_reader("{}");
        let result = json_reader.read_seeked_multi(&multi_json_path![?"x"], true, |_| {
            panic!("should not have been called");
        });
        assert_eq!(
            "no matching value found for path '.x?' at path '$', line 0, column 0 (data pos 0)",
            result.unwrap_err().to_string()
        );

        // Error: Wrong JSON value type
        let json_reader = new_reader("[]");
        let result = json_reader.read_seeked_multi(&multi_json_path![?"x"], false, |_| {
            panic!("should not have been called");
        });
        assert_eq!(
            "expected JSON value type Object but got Array at path '$', line 0, column 0 (data pos 0)",
            result.unwrap_err().to_string()
        );

        Ok(())
    }

    #[test]
    fn complex() -> Result<(), Box<dyn Error>> {
        let json_reader = new_reader(
            r#"
            {
                "a1": [
                    {
                        "a": 1,
                        "b": [
                            "v1",
                            "v2",
                            "v3"
                        ],
                        "c": true
                    },
                    {
                        "a": 1,
                        "b": [
                            "w1",
                            "w2",
                            "w3"
                        ],
                        "c": true
                    }
                ],
                "a2": [
                    {
                        "a": 1,
                        "b": [
                            "x1",
                            "x2",
                            "x3"
                        ]
                    },
                    {
                        "b": [
                            "y1",
                            "y2",
                            "y3"
                        ]
                    }
                ]
            }
            "#,
        );
        let mut values = Vec::new();
        let path = &multi_json_path![{*}, [*], "b", 1];
        json_reader.read_seeked_multi(path, true, |value_reader| {
            values.push(value_reader.read_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["v2", "w2", "x2", "y2"], values);

        let json_reader = new_reader(
            r#"
            {
                "a": 1,
                "b": [
                    {
                        "x1": {
                            "z": []
                        },
                        "x2": {
                            "y": true
                        },
                        "x3": {
                            "z": [3]
                        }
                    },
                    {
                        "x1": {
                            "y": false,
                            "z": [4, 5],
                            "a": 1.2
                        },
                        "x2": {
                        }
                    }
                ],
                "c": true
            }
            "#,
        );
        let mut values = Vec::new();
        let path = &multi_json_path!["b", [*], {*}, ?"z", [*]];
        json_reader.read_seeked_multi(path, true, |value_reader| {
            values.push(value_reader.read_number_as_string()?);
            Ok(())
        })?;
        assert_eq!(vec!["3", "4", "5"], values);

        Ok(())
    }

    /// Tests usage of `read_seeked_multi` inside of other reading methods, including nested
    /// inside another `read_seeked_multi` call
    #[test]
    fn nested() -> Result<(), Box<dyn Error>> {
        let json_reader = new_reader(
            r#"
            [
                "item-1",
                {
                    "a": [
                        "nested-1",
                        [1, 2]
                    ],
                    "b": [
                        "nested-2",
                        [3, 4]
                    ]
                },
                "item-3"
            ]
            "#,
        );
        let mut values = Vec::new();
        json_reader.read_array(|array_reader| {
            assert_eq!("item-1", array_reader.read_string()?);

            let mut member_index = 0;
            array_reader.read_seeked_multi(&multi_json_path![{*}], true, |value_reader| {
                member_index += 1;
                value_reader.read_array(|array_reader| {
                    assert_eq!(
                        format!("nested-{member_index}"),
                        array_reader.read_string()?
                    );

                    array_reader.read_seeked_multi(&multi_json_path![[*]], true, |value_reader| {
                        values.push(value_reader.read_number_as_string()?);
                        Ok(())
                    })
                })
            })?;

            assert_eq!("item-3", array_reader.read_string()?);
            Ok(())
        })?;
        // Check this outside of closure to make sure closure was called
        assert_eq!(vec!["1", "2", "3", "4"], values);

        Ok(())
    }

    #[test]
    fn error_propagation() -> Result<(), Box<dyn Error>> {
        // Should stop after the first seeking error
        let json_reader = new_reader(r#"[{"a": 1}, {}, {"a": 2}]"#);
        let mut values = Vec::new();
        let result =
            json_reader.read_seeked_multi(&multi_json_path![[*], "a"], true, |value_reader| {
                values.push(value_reader.read_number_as_string()?);
                Ok(())
            });
        assert_eq!(
            "unexpected JSON structure MissingObjectMember(\"a\") at path '$[1].<?>', line 0, column 12 (data pos 12)",
            result.unwrap_err().to_string()
        );
        // Should have already collected the first value
        assert_eq!(vec!["1"], values);

        // Should stop after closure returns error (trailing `[*]`)
        let json_reader = new_reader(r#"[1, 2, 3]"#);
        let mut call_count = 0;
        let result = json_reader.read_seeked_multi(&multi_json_path![[*]], true, |_| {
            call_count += 1;
            Err("custom-error".into())
        });
        assert_eq!("custom-error", result.unwrap_err().to_string());
        assert_eq!(1, call_count);

        // Should stop after closure returns error (non-trailing `[*]`)
        let json_reader = new_reader(r#"[{"a": 1}, {"a": 2}, {"a": 3}]"#);
        let mut call_count = 0;
        let result = json_reader.read_seeked_multi(&multi_json_path![[*], "a"], true, |_| {
            call_count += 1;
            Err("custom-error".into())
        });
        assert_eq!("custom-error", result.unwrap_err().to_string());
        assert_eq!(1, call_count);

        Ok(())
    }

    /// Tests behavior when a user-provided closure encounters an `Err` from the reader,
    /// but instead of propagating it, returns `Ok`
    #[test]
    fn discarded_error_handling() {
        let json_reader = new_reader(r#"[0, 1]"#);
        // Path with trailing `[+]`
        let result = json_reader.read_seeked_multi(&multi_json_path![[+]], true, |value_reader| {
            // Discarding error must not cause an infinite loop; `read_seeked_multi` should exit
            let result = value_reader.read_null();
            assert_eq!(
                "expected JSON value type Null but got Number at path '$[0]', line 0, column 1 (data pos 1)",
                result.unwrap_err().to_string()
            );
            Ok(())
        });
        assert_eq!(
            // Created a dummy `IncompleteDocument` error
            "syntax error: JSON syntax error IncompleteDocument at path '$[0]', line 0, column 1 (data pos 1)",
            result.unwrap_err().to_string()
        );

        let json_reader = new_reader(r#"[[0], [1]]"#);
        // Path with non-trailing `[+]`
        let result = json_reader.read_seeked_multi(&multi_json_path![[+], 0], true, |value_reader| {
            // Discarding error must not cause an infinite loop; `read_seeked_multi` should exit
            let result = value_reader.read_null();
            assert_eq!(
                "expected JSON value type Null but got Number at path '$[0][0]', line 0, column 2 (data pos 2)",
                result.unwrap_err().to_string()
            );
            Ok(())
        });
        assert_eq!(
            // Created a dummy `IncompleteDocument` error
            "syntax error: JSON syntax error IncompleteDocument at path '$[0][0]', line 0, column 2 (data pos 2)",
            result.unwrap_err().to_string()
        );

        let json_reader = new_reader(r#"[[]]"#);
        // `[+]` matching nothing
        let result = json_reader.read_array(|array_reader| {
            let result = array_reader.read_seeked_multi(&multi_json_path![[+]], true, |_| {
                panic!("should not have been called");
            });
            assert_eq!(
                "unexpected JSON structure FewerElementsThanExpected at path '$[0][0]', line 0, column 2 (data pos 2)",
                result.unwrap_err().to_string()
            );
            Ok(())
        });
        assert_eq!(
            // Created a dummy `IncompleteDocument` error
            "syntax error: JSON syntax error IncompleteDocument at path '$[0][0]', line 0, column 2 (data pos 2)",
            result.unwrap_err().to_string()
        );

        let json_reader = new_reader(r#"[{}]"#);
        // `{+}` matching nothing
        let result = json_reader.read_array(|array_reader| {
            let result = array_reader.read_seeked_multi(&multi_json_path![{+}], true, |_| {
                panic!("should not have been called");
            });
            assert_eq!(
                "unexpected JSON structure FewerElementsThanExpected at path '$[0].<?>', line 0, column 2 (data pos 2)",
                result.unwrap_err().to_string()
            );
            Ok(())
        });
        assert_eq!(
            // Created a dummy `IncompleteDocument` error
            "syntax error: JSON syntax error IncompleteDocument at path '$[0].<?>', line 0, column 2 (data pos 2)",
            result.unwrap_err().to_string()
        );

        let json_reader = new_reader(r#"[[]]"#);
        // `at_least_one_match = true` matching nothing
        let result = json_reader.read_array(|array_reader| {
            let result = array_reader.read_seeked_multi(&multi_json_path![[*]], true, |_| {
                panic!("should not have been called");
            });
            assert_eq!(
                "no matching value found for path '[*]' at path '$[0]', line 0, column 1 (data pos 1)",
                result.unwrap_err().to_string()
            );
            Ok(())
        });
        assert_eq!(
            // Created a dummy `IncompleteDocument` error
            "syntax error: JSON syntax error IncompleteDocument at path '$[0]', line 0, column 1 (data pos 1)",
            result.unwrap_err().to_string()
        );
    }
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

    // --- read_str ---
    let json_reader = new_reader("\"test\"");
    assert_error(json_reader.read_str(|_| Err(message.into())));

    // --- read_string_with_reader ---
    let json_reader = new_reader("\"test\"");
    assert_error(json_reader.read_string_with_reader(|_| Err(message.into())));

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

/// Tests behavior when a user-provided closure encounters an `Err` from the reader,
/// but instead of propagating it, returns `Ok`
#[test]
fn discarded_error_handling() {
    let json_reader = new_reader("[1]");
    let result = json_reader.read_array(|array_reader| {
        array_reader.read_null().unwrap_err();
        // Explicit read call after error
        Ok(array_reader.read_number_as_string()?)
    });
    assert_eq!(
        // Created a dummy `IncompleteDocument` error
        "syntax error: JSON syntax error IncompleteDocument at path '$[0]', line 0, column 1 (data pos 1)",
        result.unwrap_err().to_string()
    );

    let json_reader = new_reader("[1]");
    let result = json_reader.read_array(|array_reader| {
        array_reader.read_null().unwrap_err();
        Ok(())
    });
    assert_eq!(
        // Created a dummy `IncompleteDocument` error
        "syntax error: JSON syntax error IncompleteDocument at path '$[0]', line 0, column 1 (data pos 1)",
        result.unwrap_err().to_string()
    );

    let json_reader = new_reader("[1, 2]");
    let result = json_reader.read_array_items(|value_reader| {
        // Discarding error must not cause an infinite loop; `read_array_items` should exit
        value_reader.read_null().unwrap_err();
        Ok(())
    });
    assert_eq!(
        // Created a dummy `IncompleteDocument` error
        "syntax error: JSON syntax error IncompleteDocument at path '$[0]', line 0, column 1 (data pos 1)",
        result.unwrap_err().to_string()
    );

    let json_reader = new_reader(r#"{"a": 1, "b": 2}"#);
    let result = json_reader.read_object_owned_names(|_name, value_reader| {
        // Discarding error must not cause an infinite loop; `read_object_owned_names` should exit
        value_reader.read_null().unwrap_err();
        Ok(())
    });
    assert_eq!(
        // Created a dummy `IncompleteDocument` error
        "syntax error: JSON syntax error IncompleteDocument at path '$.a', line 0, column 6 (data pos 6)",
        result.unwrap_err().to_string()
    );

    let json_reader = new_reader("[]");
    let result = json_reader.read_array(|array_reader| {
        array_reader.read_null().unwrap_err();
        Ok(())
    });
    assert_eq!(
        // Created a dummy `IncompleteDocument` error
        "syntax error: JSON syntax error IncompleteDocument at path '$[0]', line 0, column 1 (data pos 1)",
        result.unwrap_err().to_string()
    );

    let json_reader = new_reader("[?]");
    let result = json_reader.read_array(|array_reader| {
        array_reader.read_null().unwrap_err();
        Ok(())
    });
    assert_eq!(
        "syntax error: JSON syntax error MalformedJson at path '$[0]', line 0, column 1 (data pos 1)",
        result.unwrap_err().to_string()
    );

    let json_reader = new_reader("[1000]");
    let result = json_reader.read_array(|array_reader| {
        array_reader.read_deserialize::<u8>().unwrap_err();
        Ok(())
    });
    assert_eq!(
        // Created a dummy `IncompleteDocument` error
        "syntax error: JSON syntax error IncompleteDocument at <location unavailable>",
        result.unwrap_err().to_string()
    );

    /// Reader which returns an EOF error (instead of 0) when the end has been reached
    struct EofReader {
        data: &'static [u8],
    }
    impl Read for EofReader {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            if self.data.is_empty() {
                return Err(std::io::Error::new(
                    ErrorKind::UnexpectedEof,
                    "custom-message",
                ));
            }
            if buf.is_empty() {
                return Ok(0);
            }

            let copy_count = min(self.data.len(), buf.len());
            buf[..copy_count].copy_from_slice(&self.data[..copy_count]);
            self.data = &self.data[copy_count..];
            Ok(copy_count)
        }
    }
    let json_reader = SimpleJsonReader::from_json_reader(JsonStreamReader::new(EofReader {
        data: r#"{"test"#.as_bytes(),
    }));
    let result = json_reader.read_object_borrowed_names(|mut member_reader| {
        let result = member_reader.read_name();
        assert_eq!(
            "IO error 'custom-message' at (roughly) path '$.<?>', line 0, column 6 (data pos 6)",
            result.unwrap_err().to_string()
        );
        member_reader.read_bool().unwrap_err();
        Ok(())
    });
    assert_eq!(
        format!(
            "IO error 'previous error '{}': custom-message' at (roughly) path '$.<?>', line 0, column 6 (data pos 6)",
            ErrorKind::UnexpectedEof
        ),
        result.unwrap_err().to_string()
    );

    let json_reader = new_reader("\"test");
    let result = json_reader.read_string_with_reader(|mut reader| {
        let mut buf = Vec::new();
        let result = reader.read_to_end(&mut buf);
        assert_eq!(
            "JSON syntax error IncompleteDocument at path '$', line 0, column 5 (data pos 5)",
            result.unwrap_err().to_string()
        );
        reader.read_to_end(&mut buf).unwrap_err();
        Ok(())
    });
    assert_eq!(
        format!(
            "IO error 'previous error '{}': JSON syntax error IncompleteDocument at path '$', line 0, column 5 (data pos 5)' at (roughly) <location unavailable>",
            ErrorKind::Other
        ),
        result.unwrap_err().to_string()
    );

    // Reading malformed UTF-8 data
    let json_reader = SimpleJsonReader::new(b"\"\xFF\"" as &[u8]);
    let result = json_reader.read_string_with_reader(|mut reader| {
        let mut buf = Vec::new();
        let result = reader.read_to_end(&mut buf);
        assert_eq!(
            "IO error 'invalid UTF-8 data' at (roughly) path '$', line 0, column 1 (data pos 1)",
            result.unwrap_err().to_string()
        );
        reader.read_to_end(&mut buf).unwrap_err();
        Ok(())
    });
    assert_eq!(
        format!(
            "IO error 'previous error '{}': IO error 'invalid UTF-8 data' at (roughly) path '$', line 0, column 1 (data pos 1)' at (roughly) <location unavailable>",
            ErrorKind::Other
        ),
        result.unwrap_err().to_string()
    );

    let json_reader = new_reader("[\"a]");
    let result = json_reader.read_array(|array_reader| {
        array_reader
            .read_string_with_reader(|_| {
                // Does not read from string; remainder should be implicitly skipped
                Ok(())
            })
            .unwrap_err();
        Ok(())
    });
    assert_eq!(
        format!(
            "IO error 'previous error '{}': JSON syntax error IncompleteDocument at path '$[0]', line 0, column 4 (data pos 4)' at (roughly) <location unavailable>",
            ErrorKind::Other
        ),
        result.unwrap_err().to_string()
    );
}
