//! Tests for [`struson::writer::simple`]

#![cfg(feature = "experimental")]
#![cfg(feature = "serde")]

use std::{
    cmp::min,
    collections::HashMap,
    error::Error,
    fmt::Debug,
    io::{sink, ErrorKind, Sink, Write},
};

use struson::writer::{
    simple::{SimpleJsonWriter, ValueWriter},
    JsonStreamWriter,
};

#[test]
fn write() {
    fn assert_written<E: Debug>(
        f: impl FnOnce(SimpleJsonWriter<JsonStreamWriter<&mut Vec<u8>>>) -> Result<(), E>,
        expected_json: &str,
    ) {
        let mut writer = Vec::new();
        let json_writer = SimpleJsonWriter::new(&mut writer);
        f(json_writer).unwrap();

        let json = String::from_utf8(writer).unwrap();
        assert_eq!(expected_json, json);
    }

    assert_written(|j| j.write_null(), "null");
    assert_written(|j| j.write_bool(true), "true");
    assert_written(|j| j.write_string("test"), "\"test\"");
    assert_written(|j| j.write_number(1_u64), "1");
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
            Ok::<(), Box<dyn Error>>(())
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
            Ok::<(), Box<dyn Error>>(())
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

/// Tests behavior when a user-provided closure discards errors and does not
/// propagate them
#[test]
fn discarded_error_handling() {
    fn new_writer() -> SimpleJsonWriter<JsonStreamWriter<Sink>> {
        SimpleJsonWriter::new(sink())
    }

    let json_writer = new_writer();
    let result = json_writer.write_array(|array_writer| {
        let _ = array_writer.write_fp_number(f32::NAN);
        Ok(())
    });
    assert_eq!(
        format!(
            "previous error '{}': non-finite number: {}",
            ErrorKind::Other,
            f32::NAN
        ),
        result.unwrap_err().to_string()
    );

    let json_writer = new_writer();
    let result = json_writer.write_object(|object_writer| {
        let _ = object_writer.write_fp_number_member("name", f32::NAN);
        Ok(())
    });
    assert_eq!(
        format!(
            "previous error '{}': non-finite number: {}",
            ErrorKind::Other,
            f32::NAN
        ),
        result.unwrap_err().to_string()
    );

    let json_writer = new_writer();
    let result = json_writer.write_array(|array_writer| {
        let _ = array_writer.write_number_string("invalid");
        Ok(())
    });
    assert_eq!(
        format!(
            "previous error '{}': invalid JSON number: invalid",
            ErrorKind::Other
        ),
        result.unwrap_err().to_string()
    );

    let json_writer = new_writer();
    let result = json_writer.write_array(|array_writer| {
        let _ = array_writer.write_serialize(&f32::NAN);
        Ok(())
    });
    assert_eq!(
        format!(
            "previous error '{}': invalid number: non-finite number: {}",
            ErrorKind::Other,
            f32::NAN
        ),
        result.unwrap_err().to_string()
    );

    let json_writer = new_writer();
    let result = json_writer.write_array(|array_writer| {
        let value = HashMap::from([(vec![1, 2], true)]);
        let _ = array_writer.write_serialize(&value);
        Ok(())
    });
    assert_eq!(
        format!(
            "previous error '{}': map key cannot be converted to string",
            ErrorKind::Other
        ),
        result.unwrap_err().to_string()
    );

    /// Writer which only permits a certain amount of bytes, returning an error afterwards
    struct MaxCapacityWriter {
        remaining_capacity: usize,
    }
    impl Write for MaxCapacityWriter {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            if self.remaining_capacity == 0 {
                return Err(std::io::Error::new(ErrorKind::WouldBlock, "custom-error"));
            }

            let write_count = min(self.remaining_capacity, buf.len());
            self.remaining_capacity -= write_count;
            Ok(write_count)
        }

        fn flush(&mut self) -> std::io::Result<()> {
            // Do nothing
            Ok(())
        }
    }
    let json_writer =
        SimpleJsonWriter::from_json_writer(JsonStreamWriter::new(MaxCapacityWriter {
            remaining_capacity: 4,
        }));
    let result = json_writer.write_array(|array_writer| {
        // Must write long enough value to trigger flushing of JsonStreamWriter's buffer
        let value = "a".repeat(1024 + 10);
        let _ = array_writer.write_string(&value);
        Ok(())
    });
    assert_eq!(
        format!("previous error '{}': custom-error", ErrorKind::WouldBlock),
        result.unwrap_err().to_string()
    )
}
