use std::{error::Error, io::Sink, iter};

use criterion::{criterion_group, criterion_main, Criterion};
use ron::writer::{JsonStreamWriter, JsonWriter, WriterSettings};
use serde::Serialize;

#[derive(Serialize, Clone)]
struct StructValue {
    bool_value: bool,
    integer: u32,
    float: f64,
    string: &'static str,
}

fn benchmark_struct(c: &mut Criterion) {
    let mut group = c.benchmark_group("write-structs");
    let values: Vec<StructValue> = iter::repeat(StructValue {
        bool_value: true,
        integer: 123456,
        float: 123.4567,
        string: "a string value with some text",
    })
    .take(10_000)
    .collect();

    fn ron_write(
        mut json_writer: JsonStreamWriter<Sink>,
        values: &Vec<StructValue>,
    ) -> Result<(), Box<dyn Error>> {
        // Hopefully this is a fair comparison with how Serde behaves
        json_writer.begin_array()?;
        for value in values {
            json_writer.begin_object()?;

            json_writer.name("bool_value")?;
            json_writer.bool_value(value.bool_value)?;

            json_writer.name("integer")?;
            json_writer.number_value(value.integer)?;

            json_writer.name("float")?;
            json_writer.fp_number_value(value.float)?;

            json_writer.name("string")?;
            json_writer.string_value(value.string)?;

            json_writer.end_object()?;
        }
        json_writer.end_array()?;

        json_writer.finish_document()?;
        Ok(())
    }

    group.bench_with_input("ron", &values, |b, values| {
        b.iter(|| {
            let json_writer = JsonStreamWriter::new(std::io::sink());
            ron_write(json_writer, &values).unwrap()
        })
    });
    group.bench_with_input("ron (pretty)", &values, |b, values| {
        b.iter(|| {
            let json_writer = JsonStreamWriter::new_custom(
                std::io::sink(),
                WriterSettings {
                    pretty_print: true,
                    ..Default::default()
                },
            );
            ron_write(json_writer, &values).unwrap()
        })
    });

    group.bench_with_input("serde", &values, |b, values| {
        b.iter(|| {
            serde_json::to_writer(std::io::sink(), &values).unwrap();
        })
    });
    group.bench_with_input("serde (pretty)", &values, |b, values| {
        b.iter(|| {
            serde_json::to_writer_pretty(std::io::sink(), &values).unwrap();
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    // Benchmark functions
    benchmark_struct
);
criterion_main!(benches);
