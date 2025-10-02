use std::{error::Error, hint::black_box, io::Write};

use criterion::{Criterion, criterion_group, criterion_main};
use serde::Serialize;
use struson::writer::{JsonStreamWriter, JsonWriter, WriterSettings};

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

#[derive(Serialize, Clone)]
struct StructValue {
    bool_value: bool,
    integer: u32,
    float: f64,
    string: &'static str,
}

fn benchmark_struct(c: &mut Criterion) {
    let mut group = c.benchmark_group("write-structs");
    let values: Vec<StructValue> = std::iter::repeat_n(
        StructValue {
            bool_value: true,
            integer: 123456,
            float: 123.4567,
            string: "a string value with some text",
        },
        10_000,
    )
    .collect();

    fn struson_write(
        mut json_writer: impl JsonWriter,
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

    group.bench_with_input("struson", &values, |b, values| {
        b.iter(|| {
            let json_writer = JsonStreamWriter::new(BlackBoxWriter);
            struson_write(json_writer, values).unwrap()
        })
    });
    group.bench_with_input("struson (pretty)", &values, |b, values| {
        b.iter(|| {
            let json_writer = JsonStreamWriter::new_custom(
                BlackBoxWriter,
                WriterSettings {
                    pretty_print: true,
                    ..Default::default()
                },
            );
            struson_write(json_writer, values).unwrap()
        })
    });

    group.bench_with_input("serde", &values, |b, values| {
        b.iter(|| {
            serde_json::to_writer(BlackBoxWriter, &values).unwrap();
        })
    });
    group.bench_with_input("serde (pretty)", &values, |b, values| {
        b.iter(|| {
            serde_json::to_writer_pretty(BlackBoxWriter, &values).unwrap();
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
