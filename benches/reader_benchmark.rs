use std::error::Error;

use criterion::{criterion_group, criterion_main, Criterion};
use serde::{de::Visitor, Deserializer};
use serde_json::de::{IoRead, Read, StrRead};
use struson::reader::*;

fn call_unwrap<F: FnOnce() -> Result<(), Box<dyn Error>>>(f: F) {
    f().unwrap();
}

fn bench_compare(c: &mut Criterion, name: &str, json: &str) {
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
                            json_reader.next_name()?;
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
                    json_reader.next_str()?;
                }
                ValueType::Number => {
                    json_reader.next_number_as_str()?;
                }
                ValueType::Boolean => {
                    json_reader.next_bool()?;
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

    fn serde_skip<'a, R: Read<'a>>(read: R) {
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

    group.bench_with_input("serde-skip (reader)", json, |b, json| {
        b.iter(|| {
            serde_skip(IoRead::new(json.as_bytes()));
        })
    });

    group.bench_with_input("serde-skip (string)", json, |b, json| {
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
    bench_compare(c, "read-large-array", &json);
}

fn benchmark_nested_object(c: &mut Criterion) {
    let count = 1000;
    let json = r#"{"member name":"#.repeat(count) + "true" + "}".repeat(count).as_str();
    bench_compare(c, "read-nested-object", &json);
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

    bench_compare(c, "read-nested-object-pretty", &json);
}

fn bench_compare_string_reading(c: &mut Criterion, name: &str, json: &str) {
    let mut group = c.benchmark_group(name);

    group.bench_with_input("struson", json, |b, json| {
        b.iter(|| {
            call_unwrap(|| {
                let mut json_reader = JsonStreamReader::new(json.as_bytes());
                json_reader.next_str()?;
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

        fn visit_borrowed_str<E: serde::de::Error>(self, _: &'de str) -> Result<Self::Value, E> {
            Ok(())
        }

        fn visit_str<E: serde::de::Error>(self, _: &str) -> Result<Self::Value, E> {
            Ok(())
        }

        fn visit_string<E: serde::de::Error>(self, _: String) -> Result<Self::Value, E> {
            Ok(())
        }
    }

    fn serde_read<'a, R: Read<'a>, F: FnOnce(&mut serde_json::de::Deserializer<R>)>(
        read: R,
        read_function: F,
    ) {
        let mut deserializer = serde_json::de::Deserializer::new(read);
        read_function(&mut deserializer);
        deserializer.end().unwrap();
    }

    // TODO: Are really all of these Serde benchmarks necessary?
    group.bench_with_input("serde-str (reader)", json, |b, json| {
        b.iter(|| {
            serde_read(IoRead::new(json.as_bytes()), |deserializer| {
                deserializer.deserialize_str(StringVisitor).unwrap()
            });
        })
    });

    group.bench_with_input("serde-string (reader)", json, |b, json| {
        b.iter(|| {
            serde_read(IoRead::new(json.as_bytes()), |deserializer| {
                deserializer.deserialize_str(StringVisitor).unwrap()
            });
        })
    });

    group.bench_with_input("serde-str (string)", json, |b, json| {
        b.iter(|| {
            serde_read(StrRead::new(json), |deserializer| {
                deserializer.deserialize_string(StringVisitor).unwrap()
            });
        })
    });

    group.bench_with_input("serde-string (string)", json, |b, json| {
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
    bench_compare(c, "read-large-ascii-string", &json);
    bench_compare_string_reading(c, "read-large-ascii-string (string reading)", &json);
}

fn benchmark_large_unicode_string(c: &mut Criterion) {
    let json = format!(
        "\"{}\"",
        "ab\u{0080}cd\u{0800}ef\u{1234}gh\u{10FFFF}".repeat(10_000)
    );
    bench_compare(c, "read-large-unicode-string", &json);
    bench_compare_string_reading(c, "read-large-unicode-string (string reading)", &json);
}

fn benchmark_escapes_string(c: &mut Criterion) {
    let json = format!(
        "\"{}\"",
        r#"a\nb\tc\\d\"e\u0000f\u0080g\u0800h\u1234i\uD800\uDC00"#.repeat(10_000)
    );
    bench_compare(c, "read-large-escapes-string", &json);
    bench_compare_string_reading(c, "read-large-escapes-string (string reading)", &json);
}

criterion_group!(
    benches,
    // Benchmark functions
    benchmark_large_array,
    benchmark_nested_object,
    benchmark_nested_object_pretty,
    benchmark_large_ascii_string,
    benchmark_large_unicode_string,
    benchmark_escapes_string
);
criterion_main!(benches);
