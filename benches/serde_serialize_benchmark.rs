use std::{hint::black_box, io::Write};

use criterion::{Criterion, criterion_group, criterion_main};
use serde::Serialize;
use struson::{
    serde::JsonWriterSerializer,
    writer::{JsonStreamWriter, JsonWriter},
};

struct BlackBoxWriter;
impl Write for BlackBoxWriter {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        black_box(buf);
        Ok(buf.len())
    }

    fn write_all(&mut self, buf: &[u8]) -> std::io::Result<()> {
        black_box(buf);
        Ok(())
    }

    fn write_fmt(&mut self, args: std::fmt::Arguments<'_>) -> std::io::Result<()> {
        black_box(args);
        Ok(())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn bench_compare<S: Serialize>(c: &mut Criterion, name: &str, value: S) {
    let mut group = c.benchmark_group(name);
    group.bench_with_input("struson", &value, |b, value| {
        b.iter(|| {
            let mut json_writer = JsonStreamWriter::new(BlackBoxWriter);
            let mut serializer = JsonWriterSerializer::new(&mut json_writer);
            value.serialize(&mut serializer).unwrap();
            json_writer.finish_document().unwrap();
        });
    });
    group.bench_with_input("serde-json", &value, |b, value| {
        b.iter(|| {
            serde_json::to_writer(BlackBoxWriter, value).unwrap();
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
