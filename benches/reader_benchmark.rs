use std::{error::Error, hint::black_box};

use criterion::{Criterion, criterion_group, criterion_main};
use serde::{Deserializer, de::Visitor};
use serde_json::de::{IoRead, StrRead};
use struson::reader::*;

fn call_unwrap<F: FnOnce() -> Result<(), Box<dyn Error>>>(f: F) {
    f().unwrap();
}

fn bench_compare(c: &mut Criterion, name: &str, json: &str, include_no_path_tracking: bool) {
    let mut group = c.benchmark_group(name);
    group.bench_with_input("struson-skip", json, |b, json| {
        b.iter(|| {
            call_unwrap(|| {
                let mut json_reader = JsonStreamReader::new_custom(
                    json.as_bytes(),
                    ReaderSettings {
                        max_nesting_depth: None,
                        ..Default::default()
                    },
                );
                json_reader.skip_value()?;
                json_reader.consume_trailing_whitespace()?;
                Ok(())
            });
        })
    });
    if include_no_path_tracking {
        group.bench_with_input("struson-skip (no path tracking)", json, |b, json| {
            b.iter(|| {
                call_unwrap(|| {
                    let mut json_reader = JsonStreamReader::new_custom(
                        json.as_bytes(),
                        ReaderSettings {
                            track_path: false,
                            max_nesting_depth: None,
                            ..Default::default()
                        },
                    );
                    json_reader.skip_value()?;
                    json_reader.consume_trailing_whitespace()?;
                    Ok(())
                });
            })
        });
    }

    fn struson_read<R: std::io::Read>(
        mut json_reader: JsonStreamReader<R>,
    ) -> Result<(), Box<dyn Error>> {
        enum StackValue {
            Array,
            Object,
        }

        let mut stack = Vec::new();
        loop {
            if !stack.is_empty() {
                match stack.last().unwrap() {
                    StackValue::Array => {
                        if !json_reader.has_next()? {
                            stack.pop();
                            json_reader.end_array()?;

                            if stack.is_empty() {
                                break;
                            } else {
                                continue;
                            }
                        }
                    }
                    StackValue::Object => {
                        if json_reader.has_next()? {
                            black_box(json_reader.next_name()?);
                            // fall through to value reading
                        } else {
                            stack.pop();
                            json_reader.end_object()?;

                            if stack.is_empty() {
                                break;
                            } else {
                                continue;
                            }
                        }
                    }
                }
            }

            match json_reader.peek()? {
                ValueType::Array => {
                    json_reader.begin_array()?;
                    stack.push(StackValue::Array)
                }
                ValueType::Object => {
                    json_reader.begin_object()?;
                    stack.push(StackValue::Object)
                }
                ValueType::String => {
                    black_box(json_reader.next_str()?);
                }
                ValueType::Number => {
                    black_box(json_reader.next_number_as_str()?);
                }
                ValueType::Boolean => {
                    black_box(json_reader.next_bool()?);
                }
                ValueType::Null => json_reader.next_null()?,
            }

            if stack.is_empty() {
                break;
            }
        }
        json_reader.consume_trailing_whitespace()?;
        Ok(())
    }

    group.bench_with_input("struson-read", json, |b, json| {
        b.iter(|| {
            call_unwrap(|| {
                let json_reader = JsonStreamReader::new_custom(
                    json.as_bytes(),
                    ReaderSettings {
                        max_nesting_depth: None,
                        ..Default::default()
                    },
                );
                struson_read(json_reader)
            });
        })
    });

    if include_no_path_tracking {
        group.bench_with_input("struson-read (no path tracking)", json, |b, json| {
            b.iter(|| {
                call_unwrap(|| {
                    let json_reader = JsonStreamReader::new_custom(
                        json.as_bytes(),
                        ReaderSettings {
                            track_path: false,
                            max_nesting_depth: None,
                            ..Default::default()
                        },
                    );
                    struson_read(json_reader)
                });
            })
        });
    }

    fn serde_skip<'a, R: serde_json::de::Read<'a>>(read: R) {
        struct UnitVisitor;

        impl Visitor<'_> for UnitVisitor {
            type Value = ();

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(formatter, "unit")
            }

            fn visit_unit<E>(self) -> Result<Self::Value, E> {
                Ok(())
            }
        }

        let mut deserializer = serde_json::de::Deserializer::new(read);
        // TODO: Is this correct?
        deserializer.deserialize_ignored_any(UnitVisitor).unwrap();
        deserializer.end().unwrap();
    }

    group.bench_with_input("serde-skip (from reader)", json, |b, json| {
        b.iter(|| {
            serde_skip(IoRead::new(json.as_bytes()));
        })
    });

    group.bench_with_input("serde-skip (from string)", json, |b, json| {
        b.iter(|| {
            serde_skip(StrRead::new(json));
        })
    });

    // TODO: Is there a way to also write a serde_json benchmark which just reads the JSON values,
    // without deserializing them into something?

    group.finish();
}

fn benchmark_large_array(c: &mut Criterion) {
    let json = format!(
        "[{}true]",
        "true, false, null, 12345689.123e12, \"abcdabcdabcdabcd\",".repeat(1000)
    );
    bench_compare(c, "read-large-array", &json, true);
}

fn benchmark_nested_object(c: &mut Criterion) {
    let count = 1000;
    let json = r#"{"member name":"#.repeat(count) + "true" + "}".repeat(count).as_str();
    bench_compare(c, "read-nested-object", &json, true);
}

fn benchmark_nested_object_pretty(c: &mut Criterion) {
    let count = 1000;
    let mut json = "{".to_owned();

    for i in 1..=count {
        json.push('\n');
        json.push_str("  ".repeat(i).as_str());
        json.push_str(r#""member name": {"#);
    }
    for i in (0..=count).rev() {
        json.push('\n');
        json.push_str("  ".repeat(i).as_str());
        json.push('}');
    }

    bench_compare(c, "read-nested-object-pretty", &json, true);
}

fn bench_compare_string_reading(c: &mut Criterion, name: &str, json: &str) {
    let mut group = c.benchmark_group(name);

    group.bench_with_input("struson", json, |b, json| {
        b.iter(|| {
            call_unwrap(|| {
                let mut json_reader = JsonStreamReader::new(json.as_bytes());
                black_box(json_reader.next_str()?);
                json_reader.consume_trailing_whitespace()?;

                Ok(())
            });
        })
    });

    struct StringVisitor;

    impl<'de> Visitor<'de> for StringVisitor {
        type Value = ();

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(formatter, "a string")
        }

        fn visit_borrowed_str<E: serde::de::Error>(self, v: &'de str) -> Result<Self::Value, E> {
            black_box(v);
            Ok(())
        }

        fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<Self::Value, E> {
            black_box(v);
            Ok(())
        }

        fn visit_string<E: serde::de::Error>(self, v: String) -> Result<Self::Value, E> {
            black_box(v);
            Ok(())
        }
    }

    fn serde_read<
        'a,
        R: serde_json::de::Read<'a>,
        F: FnOnce(&mut serde_json::de::Deserializer<R>),
    >(
        read: R,
        read_function: F,
    ) {
        let mut deserializer = serde_json::de::Deserializer::new(read);
        read_function(&mut deserializer);
        deserializer.end().unwrap();
    }

    // TODO: Are really all of these Serde benchmarks necessary?
    group.bench_with_input("serde-str (from reader)", json, |b, json| {
        b.iter(|| {
            serde_read(IoRead::new(json.as_bytes()), |deserializer| {
                deserializer.deserialize_str(StringVisitor).unwrap()
            });
        })
    });

    group.bench_with_input("serde-string (from reader)", json, |b, json| {
        b.iter(|| {
            serde_read(IoRead::new(json.as_bytes()), |deserializer| {
                deserializer.deserialize_string(StringVisitor).unwrap()
            });
        })
    });

    group.bench_with_input("serde-str (from string)", json, |b, json| {
        b.iter(|| {
            serde_read(StrRead::new(json), |deserializer| {
                deserializer.deserialize_str(StringVisitor).unwrap()
            });
        })
    });

    group.bench_with_input("serde-string (from string)", json, |b, json| {
        b.iter(|| {
            serde_read(StrRead::new(json), |deserializer| {
                deserializer.deserialize_string(StringVisitor).unwrap()
            });
        })
    });

    group.finish();
}

fn benchmark_large_ascii_string(c: &mut Criterion) {
    let json = format!("\"{}\"", "this is a test string".repeat(10_000));
    bench_compare(
        c,
        "read-large-ascii-string",
        &json,
        // Path tracking makes no difference since this is just one top-level value
        false,
    );
    bench_compare_string_reading(c, "read-large-ascii-string (string reading)", &json);
}

fn benchmark_large_unicode_string(c: &mut Criterion) {
    let json = format!(
        "\"{}\"",
        "ab\u{0080}cd\u{0800}ef\u{1234}gh\u{10FFFF}".repeat(10_000)
    );
    bench_compare(
        c,
        "read-large-unicode-string",
        &json,
        // Path tracking makes no difference since this is just one top-level value
        false,
    );
    bench_compare_string_reading(c, "read-large-unicode-string (string reading)", &json);
}

fn benchmark_escapes_string(c: &mut Criterion) {
    let json = format!(
        "\"{}\"",
        r#"a\nb\tc\\d\"e\u0000f\u0080g\u0800h\u1234i\uD800\uDC00"#.repeat(10_000)
    );
    bench_compare(
        c,
        "read-large-escapes-string",
        &json,
        // Path tracking makes no difference since this is just one top-level value
        false,
    );
    bench_compare_string_reading(c, "read-large-escapes-string (string reading)", &json);
}

fn benchmark_integer_number_reading(c: &mut Criterion) {
    let mut group = c.benchmark_group("read-integer-number");
    let numbers: [i64; _] = [
        0,
        -1,
        123,
        -256,
        256,
        -32768,
        32768,
        -1048576,
        1048576,
        -2147483648,
        2147483648,
        i64::MIN,
        i64::MAX,
    ];
    let numbers = numbers.repeat(100);
    let json = format!(
        "[{}]",
        numbers
            .into_iter()
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join(",")
    );

    group.bench_with_input("struson (next_number)", &json, |b, json| {
        b.iter(|| {
            call_unwrap(|| {
                let mut json_reader = JsonStreamReader::new(json.as_bytes());
                json_reader.begin_array()?;
                while json_reader.has_next()? {
                    black_box(json_reader.next_number::<i64>()??);
                }
                json_reader.end_array()?;
                json_reader.consume_trailing_whitespace()?;

                Ok(())
            });
        })
    });

    group.bench_with_input("struson (next_number_int)", &json, |b, json| {
        b.iter(|| {
            call_unwrap(|| {
                let mut json_reader = JsonStreamReader::new(json.as_bytes());
                json_reader.begin_array()?;
                while json_reader.has_next()? {
                    black_box(json_reader.next_number_int::<i64>()?);
                }
                json_reader.end_array()?;
                json_reader.consume_trailing_whitespace()?;

                Ok(())
            });
        })
    });

    struct NumberSeqVisitor;

    impl<'de> Visitor<'de> for NumberSeqVisitor {
        type Value = ();

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(formatter, "a seq")
        }

        fn visit_seq<A: serde::de::SeqAccess<'de>>(
            self,
            mut seq: A,
        ) -> Result<Self::Value, A::Error> {
            while let Some(number) = seq.next_element::<i64>()? {
                black_box(number);
            }
            Ok(())
        }
    }

    fn serde_read<
        'a,
        R: serde_json::de::Read<'a>,
        F: FnOnce(&mut serde_json::de::Deserializer<R>),
    >(
        read: R,
        read_function: F,
    ) {
        let mut deserializer = serde_json::de::Deserializer::new(read);
        read_function(&mut deserializer);
        deserializer.end().unwrap();
    }

    group.bench_with_input("serde (from reader)", &json, |b, json| {
        b.iter(|| {
            serde_read(IoRead::new(json.as_bytes()), |deserializer| {
                deserializer.deserialize_seq(NumberSeqVisitor).unwrap()
            });
        })
    });

    group.bench_with_input("serde (from string)", &json, |b, json| {
        b.iter(|| {
            serde_read(StrRead::new(json), |deserializer| {
                deserializer.deserialize_seq(NumberSeqVisitor).unwrap()
            });
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    // Benchmark functions
    benchmark_large_array,
    benchmark_nested_object,
    benchmark_nested_object_pretty,
    benchmark_large_ascii_string,
    benchmark_large_unicode_string,
    benchmark_escapes_string,
    benchmark_integer_number_reading,
);
criterion_main!(benches);
