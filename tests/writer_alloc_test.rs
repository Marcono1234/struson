use std::{error::Error, io::Write};

use assert_no_alloc::permit_alloc;
// Only use import when creating debug builds, see also configuration below
#[cfg(debug_assertions)]
use assert_no_alloc::AllocDisabler;
use struson::writer::{
    CompactPrettyPrinter, JsonStreamWriter, JsonWriter, SimplePrettyPrinter, StringValueWriter,
    WriterSettings,
};

// Only enable when creating debug builds
#[cfg(debug_assertions)]
#[global_allocator]
static A: AllocDisabler = AllocDisabler;

fn assert_no_alloc<F: FnOnce() -> Result<(), Box<dyn Error>>>(func: F) {
    assert_no_alloc::assert_no_alloc(func).unwrap()
}

fn permit_dealloc<T, F: FnOnce() -> T>(func: F) -> T {
    // TODO: Permitting only dealloc is not possible yet, see https://github.com/Windfisch/rust-assert-no-alloc/issues/15
    permit_alloc(func)
}

fn new_byte_writer() -> Vec<u8> {
    // Pre-allocate to avoid allocations during test execution
    Vec::with_capacity(4096)
}

#[test]
fn write_values() {
    let mut writer = new_byte_writer();
    let mut json_writer = JsonStreamWriter::new_custom(
        &mut writer,
        WriterSettings {
            // To test creation of surrogate pair escape sequences for supplementary code points
            escape_all_non_ascii: true,
            ..Default::default()
        },
        CompactPrettyPrinter,
    );

    let large_string = "abcd".repeat(500);

    assert_no_alloc(|| {
        json_writer.begin_object()?;
        json_writer.name("a")?;

        json_writer.begin_array()?;
        // Write string which has to be escaped
        json_writer.string_value("\0\n\t \u{10FFFF}")?;
        json_writer.string_value(&large_string)?;
        // Note: Cannot use non-string number methods because they perform allocation
        json_writer.number_value_from_string("1234.56e-7")?;
        json_writer.bool_value(true)?;
        json_writer.bool_value(false)?;
        json_writer.null_value()?;
        json_writer.end_array()?;

        // Write string which has to be escaped
        json_writer.name("\0\n\t \u{10FFFF}")?;
        json_writer.bool_value(true)?;

        json_writer.end_object()?;

        permit_dealloc(|| json_writer.finish_document())?;
        Ok(())
    });

    let expected_json = "{\"a\":[\"\\u0000\\n\\t \\uDBFF\\uDFFF\",\"".to_owned()
        + &large_string
        + "\",1234.56e-7,true,false,null],\"\\u0000\\n\\t \\uDBFF\\uDFFF\":true}";
    assert_eq!(expected_json, String::from_utf8(writer).unwrap());
}

#[test]
fn pretty_print() {
    let mut writer = new_byte_writer();
    let mut json_writer =
        JsonStreamWriter::new_custom(&mut writer, WriterSettings::default(), SimplePrettyPrinter);

    assert_no_alloc(|| {
        json_writer.begin_object()?;
        json_writer.name("a")?;
        json_writer.begin_array()?;

        json_writer.begin_array()?;
        json_writer.end_array()?;
        json_writer.begin_object()?;
        json_writer.end_object()?;
        json_writer.bool_value(true)?;

        json_writer.end_array()?;
        json_writer.end_object()?;

        permit_dealloc(|| json_writer.finish_document())?;
        Ok(())
    });

    let expected_json = "{\n  \"a\": [\n    [],\n    {},\n    true\n  ]\n}";
    assert_eq!(expected_json, String::from_utf8(writer).unwrap());
}

#[test]
fn string_value_writer() -> Result<(), Box<dyn Error>> {
    let mut writer = new_byte_writer();
    let mut json_writer = JsonStreamWriter::new(&mut writer);
    let large_string = "abcd".repeat(500);

    assert_no_alloc(|| {
        let mut string_value_writer = json_writer.string_value_writer()?;
        string_value_writer.write_all(b"a")?;
        string_value_writer.write_all(b"\0")?;
        string_value_writer.write_all(b"\n\t")?;
        string_value_writer.write_all(large_string.as_bytes())?;
        string_value_writer.write_all(b"test")?;
        string_value_writer.finish_value()?;

        permit_dealloc(|| json_writer.finish_document())?;
        Ok(())
    });

    let expected_json = format!("\"a\\u0000\\n\\t{large_string}test\"");
    assert_eq!(expected_json, String::from_utf8(writer).unwrap());
    Ok(())
}
