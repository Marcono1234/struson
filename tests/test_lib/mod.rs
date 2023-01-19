//! Common library module for integration tests
// See https://doc.rust-lang.org/book/ch11-03-test-organization.html#submodules-in-integration-tests

use std::path::PathBuf;

pub fn get_test_data_file_path() -> PathBuf {
    // Get path of test file, see https://stackoverflow.com/a/30004252
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("tests/test_data.json");
    path
}

#[derive(PartialEq, Eq, Debug)]
pub enum JsonEvent {
    ArrayStart,
    ArrayEnd,
    ObjectStart,
    ObjectEnd,
    MemberName(String),

    StringValue(String),
    // Contains string representation of number value
    NumberValue(String),
    BoolValue(bool),
    NullValue,
}

/// Gets the events expected for the JSON document at the path returned by [`get_test_data_file_path`]
pub fn get_expected_events() -> Vec<JsonEvent> {
    vec![
        JsonEvent::ArrayStart,
        // Arrays
        JsonEvent::ArrayStart,
        JsonEvent::ArrayEnd,
        //   Array with single item
        JsonEvent::ArrayStart,
        JsonEvent::NumberValue("1".to_owned()),
        JsonEvent::ArrayEnd,
        //   Array with multiple items
        JsonEvent::ArrayStart,
        JsonEvent::NumberValue("1".to_owned()),
        JsonEvent::StringValue("a".to_owned()),
        JsonEvent::BoolValue(true),
        JsonEvent::ObjectStart,
        JsonEvent::MemberName("nested".to_owned()),
        JsonEvent::ArrayStart,
        JsonEvent::ObjectStart,
        JsonEvent::MemberName("nested2".to_owned()),
        JsonEvent::ArrayStart,
        JsonEvent::NumberValue("2".to_owned()),
        JsonEvent::ArrayEnd,
        JsonEvent::ObjectEnd,
        JsonEvent::ArrayEnd,
        JsonEvent::ObjectEnd,
        JsonEvent::ArrayEnd,
        // Objects
        JsonEvent::ObjectStart,
        JsonEvent::ObjectEnd,
        //   Object with single member
        JsonEvent::ObjectStart,
        JsonEvent::MemberName("name".to_owned()),
        JsonEvent::NumberValue("1".to_owned()),
        JsonEvent::ObjectEnd,
        //   Object with multiple members
        JsonEvent::ObjectStart,
        JsonEvent::MemberName("name1".to_owned()),
        JsonEvent::BoolValue(false),
        JsonEvent::MemberName("name2".to_owned()),
        JsonEvent::StringValue("value".to_owned()),
        JsonEvent::MemberName("name1".to_owned()),
        JsonEvent::NumberValue("2".to_owned()),
        JsonEvent::MemberName("".to_owned()),
        JsonEvent::NumberValue("3".to_owned()),
        JsonEvent::ObjectEnd,
        // Strings
        JsonEvent::StringValue("string value".to_owned()),
        JsonEvent::StringValue("\0 test \n\t \\ \"".to_owned()),
        JsonEvent::StringValue("unicode § ಀ ᠅ 𝄆".to_owned()),
        // Numbers
        JsonEvent::NumberValue("0".to_owned()),
        JsonEvent::NumberValue("-1234".to_owned()),
        JsonEvent::NumberValue("567.89".to_owned()),
        JsonEvent::NumberValue("100e-10".to_owned()),
        JsonEvent::NumberValue("6.070e+010".to_owned()),
        // Booleans
        JsonEvent::BoolValue(true),
        JsonEvent::BoolValue(false),
        JsonEvent::NullValue,
        JsonEvent::ArrayEnd,
    ]
}
