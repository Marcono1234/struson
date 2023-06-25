use std::{error::Error, fs::read_to_string};

use struson::writer::{JsonStreamWriter, JsonWriter, WriterSettings};

use crate::test_lib::{get_expected_events, get_test_data_file_path, JsonEvent};

mod test_lib;

#[test]
fn writer_test() -> Result<(), Box<dyn Error>> {
    let expected_json = read_to_string(get_test_data_file_path())?;
    // Normalize JSON document string
    let expected_json = expected_json.replace('\r', "");
    let expected_json = expected_json.trim_end();

    let mut writer = Vec::<u8>::new();
    let mut json_writer = JsonStreamWriter::new_custom(
        &mut writer,
        WriterSettings {
            pretty_print: true,
            ..Default::default()
        },
    );

    for event in get_expected_events() {
        match event {
            JsonEvent::ArrayStart => {
                json_writer.begin_array()?;
            }
            JsonEvent::ArrayEnd => {
                json_writer.end_array()?;
            }
            JsonEvent::ObjectStart => {
                json_writer.begin_object()?;
            }
            JsonEvent::ObjectEnd => {
                json_writer.end_object()?;
            }
            JsonEvent::MemberName(name) => {
                json_writer.name(&name)?;
            }
            JsonEvent::StringValue(value) => {
                json_writer.string_value(&value)?;
            }
            JsonEvent::NumberValue(value) => {
                json_writer.number_value_from_string(&value)?;
            }
            JsonEvent::BoolValue(value) => {
                json_writer.bool_value(value)?;
            }
            JsonEvent::NullValue => {
                json_writer.null_value()?;
            }
        }
    }

    json_writer.finish_document()?;

    assert_eq!(expected_json, String::from_utf8(writer)?);

    Ok(())
}
