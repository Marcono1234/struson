use std::{error::Error, hint::black_box, io::Write};

use criterion::{Criterion, criterion_group, criterion_main};
use struson::writer::{JsonStreamWriter, JsonWriter, WriterSettings};

use serde::ser::Serializer;

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

fn bench_compare<SF: Fn(&mut JsonStreamWriter<BlackBoxWriter>) -> Result<(), Box<dyn Error>>>(
    c: &mut Criterion,
    name: &str,
    struson_function: SF,
) {
    let mut group = c.benchmark_group(name);
    group.bench_with_input("struson-write", &struson_function, |b, write_function| {
        b.iter(|| {
            let mut json_writer = JsonStreamWriter::new(BlackBoxWriter);
            write_function(&mut json_writer).unwrap();
            json_writer.finish_document().unwrap();
        })
    });
    group.bench_with_input(
        "struson-write (pretty)",
        &struson_function,
        |b, write_function| {
            b.iter(|| {
                let mut json_writer = JsonStreamWriter::new_custom(
                    BlackBoxWriter,
                    WriterSettings {
                        pretty_print: true,
                        ..Default::default()
                    },
                );
                write_function(&mut json_writer).unwrap();
                json_writer.finish_document().unwrap();
            })
        },
    );

    // TODO: Maybe also try to support Serde, but Serializer API cannot be easily used for arbitrary data?
    //   Could test against serde_json's Formatter, but that might be too low level (especially string value writing)?

    group.finish();
}

fn benchmark_large_array(c: &mut Criterion) {
    bench_compare(c, "write-large-array", |json_writer| {
        json_writer.begin_array()?;

        for _ in 0..1000 {
            json_writer.bool_value(true)?;
            json_writer.number_value(123456)?;
            json_writer.fp_number_value(1234.56)?;
            json_writer.string_value("string value")?;
        }

        json_writer.end_array()?;

        Ok(())
    });
}

fn benchmark_nested_object(c: &mut Criterion) {
    bench_compare(c, "write-nested-object", |json_writer| {
        let count = 1000;

        for _ in 0..count {
            json_writer.begin_object()?;
            json_writer.name("member name")?;
        }

        json_writer.null_value()?;

        for _ in 0..count {
            json_writer.end_object()?;
        }

        Ok(())
    });
}

fn bench_compare_string_writing(c: &mut Criterion, name: &str, string_value: &str) {
    let mut group = c.benchmark_group(name);

    group.bench_with_input("struson", string_value, |b, string_value| {
        b.iter(|| {
            let mut json_writer = JsonStreamWriter::new(BlackBoxWriter);
            json_writer.string_value(string_value).unwrap();
            json_writer.finish_document().unwrap();
        })
    });

    group.bench_with_input("serde", string_value, |b, string_value| {
        b.iter(|| {
            let mut serializer = serde_json::ser::Serializer::new(BlackBoxWriter);
            serializer.serialize_str(string_value).unwrap();
        })
    });

    group.finish();
}

fn benchmark_large_ascii_string(c: &mut Criterion) {
    let string_value = "this is a test string".repeat(10_000);
    bench_compare(c, "write-large-ascii-string", |json_writer| {
        json_writer.string_value(&string_value)?;

        Ok(())
    });
    bench_compare_string_writing(
        c,
        "write-large-ascii-string (string writing)",
        &string_value,
    );
}

fn benchmark_large_unicode_string(c: &mut Criterion) {
    let string_value = "ab\u{0080}cd\u{0800}ef\u{1234}gh\u{10FFFF}".repeat(10_000);
    bench_compare(c, "write-large-unicode-string", |json_writer| {
        json_writer.string_value(&string_value)?;

        Ok(())
    });
    bench_compare_string_writing(
        c,
        "write-large-unicode-string (string writing)",
        &string_value,
    );
}

fn benchmark_escapes_string(c: &mut Criterion) {
    let string_value = r#"a\nb\tc\\d\"e\u0000f\u0080g\u0800h\u1234i\uD800\uDC00"#.repeat(10_000);
    bench_compare(c, "write-large-escapes-string", |json_writer| {
        json_writer.string_value(&string_value)?;

        Ok(())
    });
    bench_compare_string_writing(
        c,
        "write-large-escapes-string (string writing)",
        &string_value,
    );
}

criterion_group!(
    benches,
    // Benchmark functions
    benchmark_large_array,
    benchmark_nested_object,
    benchmark_large_ascii_string,
    benchmark_large_unicode_string,
    benchmark_escapes_string
);
criterion_main!(benches);
