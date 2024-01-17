//! Tests for [`struson::writer::simple`]

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

    assert_written(|j| j.write_null().map_err(|e| e.into()), "null");
    assert_written(|j| j.write_bool(true).map_err(|e| e.into()), "true");
    assert_written(|j| j.write_string("test").map_err(|e| e.into()), "\"test\"");
    assert_written(|j| j.write_number(1_u64).map_err(|e| e.into()), "1");
    assert_written(|j| j.write_fp_number(2.3_f64), "2.3");
    assert_written(|j| j.write_number_string("4.5e6"), "4.5e6");
    assert_written(|j| j.write_serialize(&"serde"), "\"serde\"");

    assert_written(
        |json_writer| {
            json_writer.write_array(|array_writer| {
                array_writer.write_null()?;
                array_writer.write_bool(true)?;
                array_writer.write_string("test")?;
                array_writer.write_number(1_u64)?;
                array_writer.write_fp_number(2.3_f64)?;
                array_writer.write_number_string("4.5e6")?;
                array_writer.write_serialize(&"serde")?;

                array_writer.write_array(|array_writer| {
                    array_writer.write_bool(false)?;
                    Ok(())
                })?;

                array_writer.write_object(|object_writer| {
                    object_writer.write_bool_member("a", false)?;
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
            json_writer.write_object(|object_writer| {
                object_writer.write_null_member("a")?;
                object_writer.write_bool_member("b", true)?;
                object_writer.write_string_member("c", "test")?;
                object_writer.write_number_member("d", 1_u64)?;
                object_writer.write_fp_number_member("e", 2.3_f64)?;
                object_writer.write_number_string_member("f", "4.5e6")?;
                object_writer.write_serialized_member("g", &"serde")?;

                object_writer.write_array_member("h", |array_writer| {
                    array_writer.write_bool(false)?;
                    Ok(())
                })?;

                object_writer.write_object_member("i", |object_writer| {
                    object_writer.write_bool_member("nested", true)?;
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

    // --- write_array ---
    let json_writer = new_writer();
    assert_error(json_writer.write_array(|_| Err(message.into())));

    let json_writer = new_writer();
    assert_error(
        json_writer.write_array(|array_writer| array_writer.write_array(|_| Err(message.into()))),
    );

    let json_writer = new_writer();
    assert_error(
        json_writer.write_array(|array_writer| array_writer.write_object(|_| Err(message.into()))),
    );

    // --- write_object ---
    let json_writer = new_writer();
    assert_error(json_writer.write_object(|_| Err(message.into())));

    let json_writer = new_writer();
    assert_error(json_writer.write_object(|object_writer| {
        object_writer.write_array_member("name", |_| Err(message.into()))
    }));

    let json_writer = new_writer();
    assert_error(json_writer.write_object(|object_writer| {
        object_writer.write_object_member("name", |_| Err(message.into()))
    }));
}
