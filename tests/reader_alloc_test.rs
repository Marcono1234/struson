// Allow `assert_eq!(true, ...)` because it is used to check a bool value and not
// a 'flag' / 'state', and `assert_eq!` makes that more explicit
#![allow(clippy::bool_assert_comparison)]

use std::error::Error;

use assert_no_alloc::permit_alloc;
// Only use import when creating debug builds, see also configuration below
#[cfg(debug_assertions)]
use assert_no_alloc::AllocDisabler;
use struson::{
    json_path,
    reader::{JsonReader, JsonStreamReader, ReaderSettings},
    writer::{JsonStreamWriter, JsonWriter},
};

// Only enable when creating debug builds
#[cfg(debug_assertions)]
#[global_allocator]
static A: AllocDisabler = AllocDisabler;

fn assert_no_alloc<F: FnOnce() -> Result<(), Box<dyn Error>>>(func: F) {
    assert_no_alloc::assert_no_alloc(func).unwrap()
}

fn new_reader(json: &str) -> JsonStreamReader<&[u8]> {
    JsonStreamReader::new_custom(
        json.as_bytes(),
        ReaderSettings {
            // Disable path tracking because that causes allocations
            track_path: false,
            ..Default::default()
        },
    )
}

#[test]
fn skip() {
    let json =
        r#"{"a": [{"b": 1, "c": [[], [2, {"d": 3, "e": "some string value"}]]}], "f": true}"#;
    let mut json_reader = new_reader(json);

    assert_no_alloc(|| {
        json_reader.skip_value()?;

        // Use permit_alloc because assert_no_alloc currently also forbids dealloc
        permit_alloc(|| json_reader.consume_trailing_whitespace())?;
        Ok(())
    });
}

#[test]
fn read_values() {
    let json = "{\"a\": [\"string\", \"\u{1234}\u{10FFFF}\", 1234.5e+6, true, false, null]}";
    let mut json_reader = new_reader(json);

    assert_no_alloc(|| {
        json_reader.begin_object()?;
        assert_eq!("a", json_reader.next_name()?);
        json_reader.begin_array()?;

        assert_eq!("string", json_reader.next_str()?);
        assert_eq!("\u{1234}\u{10FFFF}", json_reader.next_str()?);
        assert_eq!("1234.5e+6", json_reader.next_number_as_str()?);
        assert_eq!(true, json_reader.next_bool()?);
        assert_eq!(false, json_reader.next_bool()?);
        json_reader.next_null()?;

        json_reader.end_array()?;
        json_reader.end_object()?;
        // Use permit_alloc because assert_no_alloc currently also forbids dealloc
        permit_alloc(|| json_reader.consume_trailing_whitespace())?;
        Ok(())
    });
}

#[test]
fn read_string_escape_sequences() {
    let json = r#"["\n", "\t a", "a \u1234", "a \uDBFF\uDFFF b"]"#;
    let mut json_reader = new_reader(json);

    assert_no_alloc(|| {
        json_reader.begin_array()?;
        // These don't cause allocation because the internal value buffer has already
        // been allocated when the JSON reader was created, and is then reused
        assert_eq!("\n", json_reader.next_str()?);
        assert_eq!("\t a", json_reader.next_str()?);
        assert_eq!("a \u{1234}", json_reader.next_str()?);
        assert_eq!("a \u{10FFFF} b", json_reader.next_str()?);

        json_reader.end_array()?;
        // Use permit_alloc because assert_no_alloc currently also forbids dealloc
        permit_alloc(|| json_reader.consume_trailing_whitespace())?;
        Ok(())
    });
}

#[test]
fn string_value_reader() -> Result<(), Box<dyn Error>> {
    let repetition_count = 100;
    let json_string_value = "\\n \\t a \\u1234 \\uDBFF\\uDFFF \u{10FFFF}".repeat(repetition_count);
    let expected_string_value = "\n \t a \u{1234} \u{10FFFF} \u{10FFFF}".repeat(repetition_count);
    let json = format!("\"{json_string_value}\"");
    let mut json_reader = new_reader(&json);

    // Pre-allocate with expected size to avoid allocations during test execution
    let mut string_output = String::with_capacity(expected_string_value.len());

    // Obtain this here because return value is `Box<dyn ...>` and therefore performs allocation
    let mut string_value_reader = json_reader.next_string_reader()?;

    assert_no_alloc(|| {
        string_value_reader.read_to_string(&mut string_output)?;
        Ok(())
    });
    drop(string_value_reader);
    // TODO: Ideally would call this inside assert_no_alloc, but is not possible because `string_value_reader`
    // is currently created outside of it and prevents moving `json_reader` into closure
    json_reader.consume_trailing_whitespace()?;

    assert_eq!(expected_string_value, string_output);
    Ok(())
}

#[test]
#[ignore = "transfer_to calls JsonWriter.string_value_writer and that returns a `Box<dyn ...>`"]
fn transfer_to() -> Result<(), Box<dyn Error>> {
    let inner_json = r#"{"a":[{"b":1,"c":[[],[2,{"d":3,"e":"some string value"}]]}],"f":true}"#;
    let json = "{\"outer-ignored\": 1, \"outer\":[\"ignored\", ".to_owned() + inner_json + "]}";
    let mut json_reader = new_reader(&json);

    // Pre-allocate with expected size to avoid allocations during test execution
    let mut writer = Vec::<u8>::with_capacity(inner_json.len());
    let mut json_writer = JsonStreamWriter::new(&mut writer);

    let json_path = json_path!["outer", 1];

    assert_no_alloc(|| {
        json_reader.seek_to(&json_path)?;

        json_reader.transfer_to(&mut json_writer)?;
        // Use permit_alloc because assert_no_alloc currently also forbids dealloc
        permit_alloc(|| json_writer.finish_document())?;

        json_reader.skip_to_top_level()?;
        // Use permit_alloc because assert_no_alloc currently also forbids dealloc
        permit_alloc(|| json_reader.consume_trailing_whitespace())?;
        Ok(())
    });

    assert_eq!(inner_json, String::from_utf8(writer)?);
    Ok(())
}
