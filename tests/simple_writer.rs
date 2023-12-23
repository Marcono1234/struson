#![cfg(feature = "experimental")]
#![cfg(feature = "serde")]

use std::{
    error::Error,
    fmt::Debug,
    io::{sink, Sink},
};

use struson::writer::{
    simple::{SimpleJsonWriter, ValueWriter},
    JsonStreamWriter,
};

#[test]
fn write() {
    fn assert_written(
        f: impl FnOnce(SimpleJsonWriter<JsonStreamWriter<&mut Vec<u8>>>) -> Result<(), Box<dyn Error>>,
        expected_json: &str,
    ) {
        let mut writer = Vec::new();
        let json_writer = SimpleJsonWriter::new(&mut writer);
        f(json_writer).unwrap();

        let json = String::from_utf8(writer).unwrap();
        assert_eq!(expected_json, json);
    }

    assert_written(|j| j.null_value().map_err(|e| e.into()), "null");
    assert_written(|j| j.bool_value(true).map_err(|e| e.into()), "true");
    assert_written(|j| j.string_value("test").map_err(|e| e.into()), "\"test\"");
    assert_written(|j| j.number_value(1_u64).map_err(|e| e.into()), "1");
    assert_written(|j| j.fp_number_value(2.3_f64), "2.3");
    assert_written(|j| j.number_string_value("4.5e6"), "4.5e6");
    assert_written(|j| j.serialize_value(&"serde"), "\"serde\"");

    assert_written(
        |json_writer| {
            json_writer.array_value(|array_writer| {
                array_writer.null_value()?;
                array_writer.bool_value(true)?;
                array_writer.string_value("test")?;
                array_writer.number_value(1_u64)?;
                array_writer.fp_number_value(2.3_f64)?;
                array_writer.number_string_value("4.5e6")?;
                array_writer.serialize_value(&"serde")?;

                array_writer.array_value(|array_writer| {
                    array_writer.bool_value(false)?;
                    Ok(())
                })?;

                array_writer.object_value(|object_writer| {
                    object_writer.bool_member("a", false)?;
                    Ok(())
                })?;

                Ok(())
            })?;
            Ok(())
        },
        "[null,true,\"test\",1,2.3,4.5e6,\"serde\",[false],{\"a\":false}]",
    );

    assert_written(
        |json_writer| {
            json_writer.object_value(|object_writer| {
                object_writer.null_member("a")?;
                object_writer.bool_member("b", true)?;
                object_writer.string_member("c", "test")?;
                object_writer.number_member("d", 1_u64)?;
                object_writer.fp_number_member("e", 2.3_f64)?;
                object_writer.number_string_member("f", "4.5e6")?;
                object_writer.serialized_member("g", &"serde")?;

                object_writer.array_member("h", |array_writer| {
                    array_writer.bool_value(false)?;
                    Ok(())
                })?;

                object_writer.object_member("i", |object_writer| {
                    object_writer.bool_member("nested", true)?;
                    Ok(())
                })?;

                Ok(())
            })?;
            Ok(())
        },
        r#"{"a":null,"b":true,"c":"test","d":1,"e":2.3,"f":4.5e6,"g":"serde","h":[false],"i":{"nested":true}}"#,
    );
}

/// Verifies that errors returned by closures are propagated and abort processing
///
/// Especially after the closure returned an error no further `JsonWriter` methods should be
/// called since that could cause a panic.
#[test]
fn closure_error_propagation() {
    fn new_writer() -> SimpleJsonWriter<JsonStreamWriter<Sink>> {
        SimpleJsonWriter::new(sink())
    }

    let message = "custom-message";
    fn assert_error<T: Debug>(result: Result<T, Box<dyn Error>>) {
        match result {
            Err(e) => assert_eq!("custom-message", e.to_string()),
            _ => panic!("unexpected result: {result:?}"),
        }
    }

    // --- array_value ---
    let json_writer = new_writer();
    assert_error(json_writer.array_value(|_| Err(message.into())));

    let json_writer = new_writer();
    assert_error(
        json_writer.array_value(|array_writer| array_writer.array_value(|_| Err(message.into()))),
    );

    let json_writer = new_writer();
    assert_error(
        json_writer.array_value(|array_writer| array_writer.object_value(|_| Err(message.into()))),
    );

    // --- object_value ---
    let json_writer = new_writer();
    assert_error(json_writer.object_value(|_| Err(message.into())));

    let json_writer = new_writer();
    assert_error(
        json_writer.object_value(|object_writer| {
            object_writer.array_member("name", |_| Err(message.into()))
        }),
    );

    let json_writer = new_writer();
    assert_error(json_writer.object_value(|object_writer| {
        object_writer.object_member("name", |_| Err(message.into()))
    }));
}
