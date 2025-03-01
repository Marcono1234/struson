//! Tests for [`struson::writer::simple`]

#![cfg(feature = "simple-api")]
#![cfg(feature = "serde")]

use std::{
    cmp::min,
    collections::HashMap,
    error::Error,
    fmt::{Debug, Display},
    io::{ErrorKind, Sink, Write, sink},
};

use struson::writer::{
    JsonStreamWriter,
    simple::{SimpleJsonWriter, ValueWriter},
};

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

#[test]
fn write_simple() {
    assert_written(|j| j.write_null(), "null");
    assert_written(|j| j.write_bool(true), "true");
    assert_written(|j| j.write_string("test"), "\"test\"");
    assert_written(|j| j.write_number(1_u64), "1");
    assert_written(|j| j.write_fp_number(2.3_f64), "2.3");
    assert_written(|j| j.write_number_string("4.5e6"), "4.5e6");
    assert_written(|j| j.write_serialize(&"serde"), "\"serde\"");
}

#[test]
fn write_array() {
    assert_written(
        |json_writer| {
            json_writer.write_array(|array_writer| {
                array_writer.write_null()?;
                array_writer.write_bool(true)?;
                array_writer.write_string("string")?;
                array_writer
                    .write_string_with_writer(|mut w| Ok(w.write_all(b"string-writer")?))?;
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
        "[null,true,\"string\",\"string-writer\",1,2.3,4.5e6,\"serde\",[false],{\"a\":false}]",
    );
}

#[test]
fn write_object() {
    assert_written(
        |json_writer| {
            json_writer.write_object(|object_writer| {
                object_writer.write_member("a", |value_writer| {
                    value_writer.write_bool(true)?;
                    Ok(())
                })?;
                object_writer.write_member("b", |_| {
                    // Writing no value will cause JSON null to be written
                    Ok(())
                })?;
                Ok(())
            })
        },
        r#"{"a":true,"b":null}"#,
    );

    assert_written(
        |json_writer| {
            json_writer.write_object(|object_writer| {
                object_writer.write_null_member("a")?;
                object_writer.write_bool_member("b", true)?;
                object_writer.write_string_member("c", "string")?;
                object_writer.write_string_member_with_writer("d", |mut w| {
                    Ok(w.write_all(b"string-writer")?)
                })?;
                object_writer.write_number_member("e", 1_u64)?;
                object_writer.write_fp_number_member("f", 2.3_f64)?;
                object_writer.write_number_string_member("g", "4.5e6")?;
                object_writer.write_serialized_member("h", &"serde")?;

                object_writer.write_array_member("i", |array_writer| {
                    array_writer.write_bool(false)?;
                    Ok(())
                })?;

                object_writer.write_object_member("j", |object_writer| {
                    object_writer.write_bool_member("nested", true)?;
                    Ok(())
                })?;

                Ok(())
            })
        },
        r#"{"a":null,"b":true,"c":"string","d":"string-writer","e":1,"f":2.3,"g":4.5e6,"h":"serde","i":[false],"j":{"nested":true}}"#,
    );
}

#[test]
fn write_string_with_writer() -> Result<(), Box<dyn Error>> {
    assert_written(
        |f| {
            f.write_string_with_writer(|_| {
                // Write nothing
                Ok(())
            })
        },
        "\"\"",
    );

    assert_written(
        |f| {
            f.write_string_with_writer(|mut w| {
                w.write_all(b"test")?;
                Ok(())
            })
        },
        "\"test\"",
    );

    assert_written(
        |f| {
            f.write_string_with_writer(|mut w| {
                w.write_str("test \u{1F600}")?;
                Ok(())
            })
        },
        "\"test \u{1F600}\"",
    );

    assert_written(
        |f| {
            f.write_string_with_writer(|mut w| {
                w.write_all(b"first \"")?;
                w.write_all(b" second")?;
                w.write_str(" third \"")?;
                w.write_all(b" fourth")?;
                Ok(())
            })
        },
        "\"first \\\" second third \\\" fourth\"",
    );

    let json_writer = SimpleJsonWriter::new(std::io::sink());
    let result = json_writer.write_string_with_writer(|mut w| {
        // Write malformed UTF-8 data
        w.write_all(b"\xFF")?;
        Ok(())
    });
    match result {
        Err(e) => assert_eq!("invalid UTF-8 data", e.to_string()),
        _ => panic!("unexpected result: {result:?}"),
    };

    let json_writer = SimpleJsonWriter::new(std::io::sink());
    let result = json_writer.write_string_with_writer(|mut w| {
        // Write incomplete UTF-8 data
        w.write_all(b"\xF0")?;
        Ok(())
    });
    match result {
        Err(e) => assert_eq!("incomplete multi-byte UTF-8 data", e.to_string()),
        _ => panic!("unexpected result: {result:?}"),
    };

    #[derive(Debug, PartialEq)]
    enum WriterAction {
        Flush,
        Write(Vec<u8>),
    }
    struct TrackingWriter {
        actions: Vec<WriterAction>,
    }
    impl Write for TrackingWriter {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.actions.push(WriterAction::Write(buf.to_vec()));
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            self.actions.push(WriterAction::Flush);
            Ok(())
        }
    }

    let mut tracking_writer = TrackingWriter {
        actions: Vec::new(),
    };
    let json_writer = SimpleJsonWriter::new(&mut tracking_writer);
    // Test usage of `flush()`
    json_writer.write_string_with_writer(|mut string_writer| {
        string_writer.flush()?;
        string_writer.write_all(b"first")?;
        string_writer.flush()?;
        string_writer.write_str(" second")?;
        string_writer.write_str(" third")?;
        string_writer.flush()?;
        string_writer.flush()?;
        string_writer.write_str(" fourth")?;
        Ok(())
    })?;
    assert_eq!(
        // Note: This depends a bit on the implementation details of `JsonStreamWriter`
        vec![
            WriterAction::Write(b"\"".to_vec()),
            WriterAction::Flush,
            WriterAction::Write(b"first".to_vec()),
            WriterAction::Flush,
            WriterAction::Write(b" second".to_vec()),
            WriterAction::Write(b" third".to_vec()),
            WriterAction::Flush,
            WriterAction::Flush,
            WriterAction::Write(b" fourth".to_vec()),
            WriterAction::Write(b"\"".to_vec()),
            WriterAction::Flush,
        ],
        tracking_writer.actions
    );

    Ok(())
}

/// Verifies that errors returned by closures are propagated and abort processing
///
/// Especially after the closure returned an error no further `JsonWriter` methods should be
/// called since that could cause a panic.
#[test]
fn closure_error_propagation() {
    let message = "custom-message";
    fn assert_error<T: Debug, E: Display + Debug>(
        f: impl FnOnce(SimpleJsonWriter<JsonStreamWriter<&mut Vec<u8>>>) -> Result<T, E>,
        partial_json: &str,
    ) {
        let mut writer = Vec::new();
        let json_writer = SimpleJsonWriter::new(&mut writer);
        let result = f(json_writer);
        match result {
            Err(e) => assert_eq!("custom-message", e.to_string()),
            _ => panic!("unexpected result: {result:?}"),
        };

        // Check partial written JSON data to make sure no additional data (e.g. closing `]`) was
        // written after error was propagated
        assert_eq!(partial_json, String::from_utf8(writer).unwrap());
    }

    // --- write_string_with_writer ---
    assert_error(
        |json_writer| json_writer.write_string_with_writer(|_| Err(message.into())),
        "\"",
    );

    // --- write_array ---
    assert_error(
        |json_writer| json_writer.write_array(|_| Err(message.into())),
        "[",
    );

    assert_error(
        |json_writer| {
            json_writer
                .write_array(|array_writer| array_writer.write_array(|_| Err(message.into())))
        },
        "[[",
    );

    assert_error(
        |json_writer| {
            json_writer
                .write_array(|array_writer| array_writer.write_object(|_| Err(message.into())))
        },
        "[{",
    );

    // --- write_object ---
    assert_error(
        |json_writer| json_writer.write_object(|_| Err(message.into())),
        "{",
    );

    assert_error(
        |json_writer| {
            json_writer.write_object(|object_writer| {
                object_writer.write_member("name", |_| Err(message.into()))
            })
        },
        "{\"name\":",
    );

    assert_error(
        |json_writer| {
            json_writer.write_object(|object_writer| {
                object_writer.write_array_member("name", |_| Err(message.into()))
            })
        },
        "{\"name\":[",
    );

    assert_error(
        |json_writer| {
            json_writer.write_object(|object_writer| {
                object_writer.write_object_member("name", |_| Err(message.into()))
            })
        },
        "{\"name\":{",
    );
}

/// Tests behavior when a user-provided closure encounters an `Err` from the writer,
/// but instead of propagating it, returns `Ok`
#[test]
fn discarded_error_handling() {
    fn new_writer() -> SimpleJsonWriter<JsonStreamWriter<Sink>> {
        SimpleJsonWriter::new(sink())
    }

    let json_writer = new_writer();
    let result = json_writer.write_array(|array_writer| {
        array_writer.write_fp_number(f32::NAN).unwrap_err();
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
        object_writer
            .write_fp_number_member("name", f32::NAN)
            .unwrap_err();
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
        object_writer.write_member("name", |value_writer| {
            value_writer.write_fp_number(f32::NAN).unwrap_err();
            Ok(())
        })?;
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
        array_writer.write_number_string("invalid").unwrap_err();
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
        array_writer.write_serialize(&f32::NAN).unwrap_err();
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
        array_writer.write_serialize(&value).unwrap_err();
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
    let json_writer = SimpleJsonWriter::new(MaxCapacityWriter {
        remaining_capacity: 3,
    });
    let result = json_writer.write_array(|array_writer| {
        array_writer.write_string("test").unwrap_err();
        Ok(())
    });
    assert_eq!(
        format!("previous error '{}': custom-error", ErrorKind::WouldBlock),
        result.unwrap_err().to_string()
    );

    let json_writer = new_writer();
    let result = json_writer.write_string_with_writer(|mut writer| {
        // Malformed UTF-8
        writer.write_all(b"\"\xFF\"").unwrap_err();
        Ok(())
    });
    assert_eq!(
        format!(
            "previous error '{}': invalid UTF-8 data",
            ErrorKind::InvalidData
        ),
        result.unwrap_err().to_string()
    );

    let json_writer = new_writer();
    let result = json_writer.write_string_with_writer(|mut writer| {
        // Malformed UTF-8
        writer.write_all(b"\"\xFF\"").unwrap_err();
        let result = writer.write_all(b"\"\xFF\"");
        assert_eq!(
            format!(
                "previous error '{}': invalid UTF-8 data",
                ErrorKind::InvalidData
            ),
            result.unwrap_err().to_string()
        );
        Ok(())
    });
    assert_eq!(
        format!(
            "previous error '{}': invalid UTF-8 data",
            ErrorKind::InvalidData
        ),
        result.unwrap_err().to_string()
    );

    let json_writer = SimpleJsonWriter::new(MaxCapacityWriter {
        remaining_capacity: 3,
    });
    let result = json_writer.write_string_with_writer(|mut writer| {
        writer.write_str("test").unwrap_err();
        Ok(())
    });
    assert_eq!(
        format!("previous error '{}': custom-error", ErrorKind::WouldBlock),
        result.unwrap_err().to_string()
    );

    /// Writer which returns an error when `flush()` is called
    struct FlushErrorWriter;
    impl Write for FlushErrorWriter {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            // Do nothing
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Err(std::io::Error::new(ErrorKind::WouldBlock, "custom-error"))
        }
    }
    let json_writer = SimpleJsonWriter::new(FlushErrorWriter);
    let result = json_writer.write_string_with_writer(|mut writer| {
        let error = writer.flush().unwrap_err();
        assert_eq!(ErrorKind::WouldBlock, error.kind());
        assert_eq!("custom-error", error.to_string());
        Ok(())
    });
    assert_eq!(
        format!("previous error '{}': custom-error", ErrorKind::WouldBlock),
        result.unwrap_err().to_string()
    );

    let json_writer = SimpleJsonWriter::new(sink());
    let result = json_writer.write_array(|array_writer| {
        array_writer
            .write_string_with_writer(|mut writer| {
                // Malformed UTF-8
                writer.write_all(b"\"\xFF\"").unwrap_err();
                Ok(())
            })
            .unwrap_err();
        Ok(())
    });
    assert_eq!(
        format!(
            "previous error '{}': invalid UTF-8 data",
            ErrorKind::InvalidData
        ),
        result.unwrap_err().to_string()
    );

    let json_writer = SimpleJsonWriter::new(sink());
    let result = json_writer.write_object(|object_writer| {
        object_writer
            .write_string_member_with_writer("name", |mut writer| {
                // Malformed UTF-8
                writer.write_all(b"\"\xFF\"").unwrap_err();
                Ok(())
            })
            .unwrap_err();
        Ok(())
    });
    assert_eq!(
        format!(
            "previous error '{}': invalid UTF-8 data",
            ErrorKind::InvalidData
        ),
        result.unwrap_err().to_string()
    );
}
