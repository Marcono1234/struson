use criterion::{criterion_group, criterion_main, Criterion};
use ron::{
    serde::JsonWriterSerializer,
    writer::{JsonStreamWriter, JsonWriter},
};
use serde::Serialize;

fn bench_compare<S: Serialize>(c: &mut Criterion, name: &str, value: S) {
    let mut group = c.benchmark_group(name);
    group.bench_with_input("ron", &value, |b, value| {
        b.iter(|| {
            let mut json_writer = JsonStreamWriter::new(std::io::sink());
            let mut serializer = JsonWriterSerializer::new(&mut json_writer);
            value.serialize(&mut serializer).unwrap();
            json_writer.finish_document().unwrap();
        });
    });
    group.bench_with_input("serde-json", &value, |b, value| {
        b.iter(|| {
            serde_json::to_writer(std::io::sink(), value).unwrap();
        });
    });

    group.finish();
}

fn benchmark_number_vec(c: &mut Criterion) {
    let value = (0..10)
        .map(|x| (0..10).map(|y| x * y).collect())
        .collect::<Vec<Vec<u8>>>();

    bench_compare(c, "serde-serialize-number-vec", value);
}

fn benchmark_structs(c: &mut Criterion) {
    #[derive(Serialize)]
    struct Nested {
        my_field: String,
        another_one: u32,
    }

    #[derive(Serialize)]
    enum Enum {
        VariantA,
        Other(u32),
        AndOneMore { value: bool },
    }

    #[derive(Serialize)]
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

    bench_compare(c, "serde-serialize-structs", value);
}

criterion_group!(
    benches,
    // Benchmark functions
    benchmark_number_vec,
    benchmark_structs
);
criterion_main!(benches);
