use criterion::{Criterion, criterion_group, criterion_main};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use struson::{
    reader::{JsonReader, JsonStreamReader, ReaderSettings},
    serde::JsonReaderDeserializer,
};

fn bench_compare<D: DeserializeOwned>(c: &mut Criterion, name: &str, json: &str) {
    let bytes = json.as_bytes();
    let mut group = c.benchmark_group(name);
    group.bench_with_input("struson", bytes, |b, bytes| {
        b.iter(|| {
            let mut json_reader = JsonStreamReader::new_custom(
                bytes,
                ReaderSettings {
                    // Disable path tracking for fairer comparison, because Serde JSON does not seem to track JSON path either
                    track_path: false,
                    ..Default::default()
                },
            );
            let mut deserializer = JsonReaderDeserializer::new(&mut json_reader);
            D::deserialize(&mut deserializer).unwrap();
            json_reader.consume_trailing_whitespace().unwrap();
        });
    });
    group.bench_with_input("serde-json", bytes, |b, bytes| {
        b.iter(|| {
            serde_json::from_reader::<_, D>(bytes).unwrap();
        });
    });

    group.finish();
}

fn benchmark_number_vec(c: &mut Criterion) {
    let value = (0..10)
        .map(|x| (0..10).map(|y| x * y).collect())
        .collect::<Vec<Vec<u8>>>();

    let json = serde_json::to_string(&value).unwrap();
    bench_compare::<Vec<Vec<u8>>>(c, "serde-deserialize-number-vec", &json);
}

fn benchmark_structs(c: &mut Criterion) {
    #[derive(Serialize, Deserialize)]
    struct Nested {
        my_field: String,
        another_one: u32,
    }

    #[derive(Serialize, Deserialize)]
    enum Enum {
        VariantA,
        Other(u32),
        AndOneMore { value: bool },
    }

    #[derive(Serialize, Deserialize)]
    struct Struct {
        name: String,
        some_value: u32,
        optional: Option<f64>,
        nested: Nested,
        enum_value: Enum,
    }

    let value = (0..30)
        .map(|i| Struct {
            name: format!("some name {i}"),
            some_value: i * 256,
            optional: if i % 5 == 0 {
                None
            } else {
                Some(i as f64 / 123.0)
            },
            nested: Nested {
                my_field: "abcd".repeat((5 + i % 10) as usize),
                another_one: i * i,
            },
            enum_value: match i % 3 {
                0 => Enum::VariantA,
                1 => Enum::Other(i * 2),
                _ => Enum::AndOneMore { value: i % 2 == 0 },
            },
        })
        .collect::<Vec<_>>();

    let json = serde_json::to_string(&value).unwrap();
    bench_compare::<Vec<Struct>>(c, "serde-deserialize-structs", &json);
}

criterion_group!(
    benches,
    // Benchmark functions
    benchmark_number_vec,
    benchmark_structs
);
criterion_main!(benches);
