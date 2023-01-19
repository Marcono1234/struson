use std::error::Error;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ron::reader::{JsonReader, JsonStreamReader, ReaderSettings};
use serde::Deserialize;
use serde_json::{
    de::{IoRead, Read, StrRead},
    StreamDeserializer,
};

#[derive(Deserialize)]
#[allow(dead_code)] // suppress warnings for not read fields
struct StructValue {
    bool_value: bool,
    integer: u32,
    float: f64,
    string: String,
}

fn benchmark_struct(c: &mut Criterion) {
    let mut group = c.benchmark_group("read-structs");

    static COUNT: usize = 5000;
    let json = r#"{"bool_value": true, "integer": 123456, "float": 1234.56, "string": "this is a string value"}"#.repeat(COUNT);
    let json = json.as_str();

    group.bench_with_input("ron", json, |b, json| {
        b.iter(|| {
            let mut json_reader = JsonStreamReader::new_custom(
                json.as_bytes(),
                ReaderSettings {
                    allow_multiple_top_level: true,
                    ..Default::default()
                },
            );

            let mut count = 0;
            // Hopefully this is a fair comparison with how Serde behaves

            || -> Result<(), Box<dyn Error>> {
                loop {
                    let mut bool_value = None;
                    let mut integer = None;
                    let mut float = None;
                    let mut string = None;

                    json_reader.begin_object()?;
                    while json_reader.has_next()? {
                        match json_reader.next_name()?.as_str() {
                            "bool_value" => {
                                bool_value = Some(json_reader.next_bool()?);
                            }
                            "integer" => {
                                integer = Some(json_reader.next_number::<u32>()??);
                            }
                            "float" => {
                                float = Some(json_reader.next_number::<f64>()??);
                            }
                            "string" => {
                                string = Some(json_reader.next_string()?);
                            }
                            name => panic!("Unknown name '{name}'"),
                        }
                    }
                    json_reader.end_object()?;
                    // Discard created struct
                    black_box(StructValue {
                        bool_value: bool_value.unwrap(),
                        integer: integer.unwrap(),
                        float: float.unwrap(),
                        string: string.unwrap(),
                    });
                    count += 1;

                    if !json_reader.has_next()? {
                        break;
                    }
                }
                assert_eq!(COUNT, count);

                Ok(())
            }()
            .unwrap();
        })
    });

    fn serde_read<'a, R: Read<'a>>(read: R) {
        let count = StreamDeserializer::<R, StructValue>::new(read)
            .map(Result::unwrap)
            .count();
        assert_eq!(COUNT, count);
    }

    group.bench_with_input("serde (reader)", &json, |b, json| {
        b.iter(|| serde_read(IoRead::new(json.as_bytes())))
    });
    group.bench_with_input("serde (string)", &json, |b, json| {
        b.iter(|| serde_read(StrRead::new(json)))
    });

    group.finish();
}

criterion_group!(
    benches,
    // Benchmark functions
    benchmark_struct
);
criterion_main!(benches);
