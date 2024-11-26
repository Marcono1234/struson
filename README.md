# <div align="center"> Struson </br> [![crates.io](https://img.shields.io/crates/v/struson)](https://crates.io/crates/struson) [![docs.rs](https://img.shields.io/docsrs/struson?label=docs.rs)](https://docs.rs/struson)</div>

Struson is an [RFC 8259](https://www.rfc-editor.org/rfc/rfc8259.html) compliant streaming JSON reader and writer.

Its main purpose is to allow reading and writing JSON documents in a memory efficient way without having to store the complete JSON document structure in memory.

The API of Struson was inspired by the streaming API of the Java library [Gson](https://github.com/google/gson) (classes `JsonReader` and `JsonWriter`). It is rather low-level and its methods correspond to the elements of a JSON document, with little abstraction on top of it, allowing to read and write any valid JSON document regardless of its structure or content.

**Note:** This library is still experimental. The performance is not very good yet and the API might be changed in future versions; releases < 1.0.0 might not follow [Semantic Versioning](https://doc.rust-lang.org/cargo/reference/semver.html), breaking changes may occur.\
Feedback and suggestions for improvements are welcome!

## Why?

The most popular JSON Rust crates [Serde JSON (`serde_json`)](https://github.com/serde-rs/json) and [json-rust (`json`)](https://github.com/maciejhirsz/json-rust) mainly provide high level APIs for working with JSON.

- Serde JSON provides an API for converting JSON into DOM like structures (module `serde_json::value`) and object mapper functionality by converting structs to JSON and vice versa. Both requires the complete value to be present in memory. The trait `serde_json::ser::Formatter` actually allows writing JSON in a streaming way, but its API is arguably too low level and inconvenient to use: You have to handle string escaping yourself, and you always have to provide the writer as argument for every method call.\
  Note however, that Serde JSON's [`StreamDeserializer`](https://docs.rs/serde_json/latest/serde_json/struct.StreamDeserializer.html) allows reading multiple top-level values in a streaming way, and that certain streaming use cases can be solved with custom `Visitor` implementations, see the documentation for examples of [streaming an array](https://serde.rs/stream-array.html) and [discarding data](https://serde.rs/ignored-any.html).

- json-rust provides an API for converting JSON into DOM like structures (enum `json::JsonValue`), this requires the complete value to be present in memory. The trait `json::codegen::Generator` offers a partial API for writing JSON in a streaming way, however it misses methods for writing JSON arrays and objects in a streaming way.

If you need to process JSON in a DOM like way or want object mapper functionality to convert structs to JSON and vice versa, then Struson is _not_ suited for your use case and you should instead use one of the libraries above.

## Main features

- Low level streaming API, no implicit value conversion
- Strong enforcement of correct API usage
- Panics only for incorrect API usage\
  Malformed JSON and unexpected JSON structure only causes errors
- API does not require recursion for JSON arrays and objects\
  Can theoretically read and write arbitrarily deeply nested JSON data
- Read and write arbitrarily precise JSON numbers as string\
  ([`JsonReader::next_number_as_str`](https://docs.rs/struson/latest/struson/reader/trait.JsonReader.html#tymethod.next_number_as_str) and [`JsonWriter::number_value_from_string`](https://docs.rs/struson/latest/struson/writer/trait.JsonWriter.html#tymethod.number_value_from_string))
- Seek to specific location in JSON data ([`JsonReader::seek_to`](https://docs.rs/struson/latest/struson/reader/trait.JsonReader.html#tymethod.seek_to))
- Transfer JSON data from a reader to a writer ([`JsonReader::transfer_to`](https://docs.rs/struson/latest/struson/reader/trait.JsonReader.html#tymethod.transfer_to))
- Read and write arbitrarily large JSON string values\
  ([`JsonReader::next_string_reader`](https://docs.rs/struson/latest/struson/reader/trait.JsonReader.html#tymethod.next_string_reader) and [`JsonWriter::string_value_writer`](https://docs.rs/struson/latest/struson/writer/trait.JsonWriter.html#tymethod.string_value_writer))
- Optional [Serde integration](#serde-integration)

## Usage examples

Two variants of the API are provided:

- simple: ensures correct API usage at compile-time
- advanced: ensures correct API usage only at runtime (by panicking); more flexible and
  provides more functionality

### Simple API

**🔬 Experimental**\
The simple API and its naming is currently experimental, please provide feedback [here](https://github.com/Marcono1234/struson/issues/34).
It has to be enabled by specifying the `simple-api` feature in `Cargo.toml`:

```toml
[dependencies]
struson = { version = "...", features = ["simple-api"] }
```

Any feedback is appreciated!

#### Reading

See [`SimpleJsonReader`](https://docs.rs/struson/latest/struson/reader/simple/struct.SimpleJsonReader.html).

```rust
use struson::reader::simple::*;

// In this example JSON data comes from a string;
// normally it would come from a file or a network connection
let json_reader = SimpleJsonReader::new(r#"["a", "short", "example"]"#.as_bytes());
let mut words = Vec::<String>::new();
json_reader.read_array_items(|item_reader| {
    let word = item_reader.read_string()?;
    words.push(word);
    Ok(())
})?;
assert_eq!(words, vec!["a", "short", "example"]);
```

For reading nested values, the methods [`read_seeked`](https://docs.rs/struson/latest/struson/reader/simple/trait.ValueReader.html#tymethod.read_seeked)
and [`read_seeked_multi`](https://docs.rs/struson/latest/struson/reader/simple/trait.ValueReader.html#tymethod.read_seeked_multi)
can be used:

```rust
use struson::reader::simple::*;
use struson::reader::simple::multi_json_path::multi_json_path;

// In this example JSON data comes from a string;
// normally it would come from a file or a network connection
let json = r#"{
    "users": [
        {"name": "John", "age": 32},
        {"name": "Jane", "age": 41}
    ]
}"#;
let json_reader = SimpleJsonReader::new(json.as_bytes());

let mut ages = Vec::<u32>::new();
// Select the ages of all users
let json_path = multi_json_path!["users", [*], "age"];
json_reader.read_seeked_multi(&json_path, false, |value_reader| {
    let age = value_reader.read_number()??;
    ages.push(age);
    Ok(())
})?;
assert_eq!(ages, vec![32, 41]);
```

#### Writing

See [`SimpleJsonWriter`](https://docs.rs/struson/latest/struson/writer/simple/struct.SimpleJsonWriter.html).

```rust
use struson::writer::simple::*;

// In this example JSON bytes are stored in a Vec;
// normally they would be written to a file or network connection
let mut writer = Vec::<u8>::new();
let json_writer = SimpleJsonWriter::new(&mut writer);
json_writer.write_object(|object_writer| {
    object_writer.write_number_member("a", 1)?;
    object_writer.write_bool_member("b", true)?;
    Ok(())
})?;

let json = String::from_utf8(writer)?;
assert_eq!(json, r#"{"a":1,"b":true}"#);
```

### Advanced API

#### Reading

See [`JsonStreamReader`](https://docs.rs/struson/latest/struson/reader/struct.JsonStreamReader.html).

```rust
use struson::reader::*;

// In this example JSON data comes from a string;
// normally it would come from a file or a network connection
let json = r#"{"a": [1, true]}"#;
let mut json_reader = JsonStreamReader::new(json.as_bytes());

json_reader.begin_object()?;
assert_eq!(json_reader.next_name()?, "a");

json_reader.begin_array()?;
assert_eq!(json_reader.next_number::<u32>()??, 1);
assert_eq!(json_reader.next_bool()?, true);
json_reader.end_array()?;

json_reader.end_object()?;
// Ensures that there is no trailing data
json_reader.consume_trailing_whitespace()?;
```

#### Writing

See [`JsonStreamWriter`](https://docs.rs/struson/latest/struson/writer/struct.JsonStreamWriter.html).

```rust
use struson::writer::*;

// In this example JSON bytes are stored in a Vec;
// normally they would be written to a file or network connection
let mut writer = Vec::<u8>::new();
let mut json_writer = JsonStreamWriter::new(&mut writer);

json_writer.begin_object()?;
json_writer.name("a")?;

json_writer.begin_array()?;
json_writer.number_value(1)?;
json_writer.bool_value(true)?;
json_writer.end_array()?;

json_writer.end_object()?;
// Ensures that the JSON document is complete and flushes the buffer
json_writer.finish_document()?;

let json = String::from_utf8(writer)?;
assert_eq!(json, r#"{"a":[1,true]}"#);
```

## Serde integration

Optional integration with [Serde](https://docs.rs/serde/latest/serde/) exists to allow writing a `Serialize` to a `JsonWriter` and reading a `Deserialize` from a `JsonReader`. See the [`serde` module](https://docs.rs/struson/latest/struson/serde/index.html) of this crate for more information.

## Changelog

See [GitHub releases](https://github.com/Marcono1234/struson/releases).

## Building

This project uses [cargo-make](https://github.com/sagiegurari/cargo-make) for building:

```sh
cargo make
```

If you don't want to install cargo-make, you can instead manually run the tasks declared in the [`Makefile.toml`](Makefile.toml).

## Similar projects

- <https://github.com/alexmaco/json_stream>
  > A streaming JSON parser/emitter library for rust
- <https://github.com/sarum90/qjsonrs>
  > JSON Tokenizer written in Rust
- <https://github.com/jeremiah-shaulov/nop-json>
  > JSON serialization/deserialization (full-featured, modern, streaming, direct into struct/enum)
- <https://github.com/isagalaev/ijson-rust>
  <!-- Note: Project itself has no README or description -->
  > Rust re-implementation of the Python streaming JSON parser [ijson](https://github.com/isagalaev/ijson)
- <https://github.com/byron/json-tools>
  > A zero-copy json-lexer, filters and serializer.
- <https://github.com/01mf02/hifijson>
  > High-fidelity JSON lexer and parser
- <https://github.com/khonsulabs/justjson>'s `justjson::parser::Tokenizer`
  > A JSON tokenizer, which converts JSON source to a series of Tokens
- <https://github.com/iovxw/jsonpull>
  > Json pull parser
- <https://github.com/zotta/json-writer-rs>
  > Simple and fast crate for writing JSON to a string without creating intermediate objects
- <https://crates.io/crates/jsn>
  > A queryable, streaming, JSON pull-parser with low allocation overhead.
- <https://github.com/michel-kraemer/actson-rs>
  > Actson is a low-level JSON parser for reactive applications and non-blocking I/O.
- [rustc-serialize `Parser`](https://docs.rs/rustc-serialize/latest/rustc_serialize/json/struct.Parser.html) (deprecated)
  > A streaming JSON parser implemented as an iterator of JsonEvent, consuming an iterator of char.

## License

Licensed under either of

- [Apache License, Version 2.0](LICENSE-APACHE)
- [MIT License](LICENSE-MIT)

at your option.

All contributions you make to this project are licensed implicitly under both licenses mentioned above, without any additional terms or conditions.

Note: This dual-licensing is the same you see for the majority of Rust projects, see also the [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/necessities.html#crate-and-its-dependencies-have-a-permissive-license-c-permissive).
