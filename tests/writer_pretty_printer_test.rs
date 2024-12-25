use std::error::Error;

use struson::{
    reader::ValueType,
    writer::{
        JsonStreamWriter, JsonWriter, PrettyPrinter, SimplePrettyPrinter, StringValueWriter,
        WriterSettings,
    },
};

type IoError = std::io::Error;

#[test]
fn pretty_printer_calls() -> Result<(), Box<dyn Error>> {
    struct CustomPrettyPrinter;
    impl CustomPrettyPrinter {
        fn write(
            data: String,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            write(b"\n<")?;
            write(data.as_bytes())?;
            write(b">\n")
        }
    }
    impl PrettyPrinter for CustomPrettyPrinter {
        fn begin_array(
            &mut self,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            Self::write(format!("begin_array({nesting_depth})"), write)
        }

        fn end_array(
            &mut self,
            nesting_depth: u32,
            is_empty: bool,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            Self::write(format!("end_array({nesting_depth}, {is_empty})"), write)
        }

        fn begin_object(
            &mut self,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            Self::write(format!("begin_object({nesting_depth})"), write)
        }

        fn end_object(
            &mut self,
            nesting_depth: u32,
            is_empty: bool,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            Self::write(format!("end_object({nesting_depth}, {is_empty})"), write)
        }

        fn before_top_level_value(
            &mut self,
            value_type: ValueType,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            Self::write(format!("before_top_level_value({value_type})"), write)
        }

        fn after_top_level_value(
            &mut self,
            value_type: ValueType,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            Self::write(format!("after_top_level_value({value_type})"), write)
        }

        fn before_array_item(
            &mut self,
            value_type: ValueType,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            Self::write(
                format!("before_array_item({value_type}, {nesting_depth})"),
                write,
            )
        }

        fn after_array_item(
            &mut self,
            value_type: ValueType,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            Self::write(
                format!("after_array_item({value_type}, {nesting_depth})"),
                write,
            )
        }

        fn before_member_name(
            &mut self,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            Self::write(format!("before_member_name({nesting_depth})"), write)
        }

        fn after_member_name(
            &mut self,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            Self::write(format!("after_member_name({nesting_depth})"), write)
        }

        fn before_member_value(
            &mut self,
            value_type: ValueType,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            Self::write(
                format!("before_member_value({value_type}, {nesting_depth})"),
                write,
            )
        }

        fn after_member_value(
            &mut self,
            value_type: ValueType,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            Self::write(
                format!("after_member_value({value_type}, {nesting_depth})"),
                write,
            )
        }
    }

    let mut writer = Vec::<u8>::new();
    let mut json_writer = JsonStreamWriter::new_custom(
        &mut writer,
        WriterSettings {
            multi_top_level_value_separator: Some("#".to_owned()),
            ..Default::default()
        },
        CustomPrettyPrinter,
    );

    json_writer.begin_array()?;
    json_writer.null_value()?;
    json_writer.bool_value(true)?;
    json_writer.number_value(123)?;
    json_writer.fp_number_value(123.4)?;
    json_writer.number_value_from_string("456")?;
    json_writer.string_value("str")?;

    let mut string_value_writer = json_writer.string_value_writer()?;
    string_value_writer.write_str("str-writer")?;
    string_value_writer.finish_value()?;

    json_writer.begin_array()?;
    json_writer.end_array()?;

    json_writer.begin_array()?;
    json_writer.null_value()?;
    json_writer.end_array()?;

    json_writer.begin_object()?;
    json_writer.end_object()?;

    json_writer.begin_object()?;
    json_writer.name("first")?;
    json_writer.bool_value(true)?;
    json_writer.end_object()?;

    json_writer.begin_object()?;
    json_writer.name("first")?;
    json_writer.bool_value(false)?;
    json_writer.name("second")?;
    json_writer.number_value(12)?;
    json_writer.end_object()?;

    json_writer.end_array()?;

    // Second top-level value
    json_writer.begin_object()?;
    json_writer.name("name")?;
    json_writer.number_value(123)?;
    json_writer.end_object()?;

    json_writer.finish_document()?;

    let json = String::from_utf8(writer)?;
    assert_eq!(
        r#"
<before_top_level_value(Array)>
[
<begin_array(1)>

<before_array_item(Null, 1)>
null
<after_array_item(Null, 1)>
,
<before_array_item(Boolean, 1)>
true
<after_array_item(Boolean, 1)>
,
<before_array_item(Number, 1)>
123
<after_array_item(Number, 1)>
,
<before_array_item(Number, 1)>
123.4
<after_array_item(Number, 1)>
,
<before_array_item(Number, 1)>
456
<after_array_item(Number, 1)>
,
<before_array_item(String, 1)>
"str"
<after_array_item(String, 1)>
,
<before_array_item(String, 1)>
"str-writer"
<after_array_item(String, 1)>
,
<before_array_item(Array, 1)>
[
<begin_array(2)>

<end_array(2, true)>
]
<after_array_item(Array, 1)>
,
<before_array_item(Array, 1)>
[
<begin_array(2)>

<before_array_item(Null, 2)>
null
<after_array_item(Null, 2)>

<end_array(2, false)>
]
<after_array_item(Array, 1)>
,
<before_array_item(Object, 1)>
{
<begin_object(2)>

<end_object(2, true)>
}
<after_array_item(Object, 1)>
,
<before_array_item(Object, 1)>
{
<begin_object(2)>

<before_member_name(2)>
"first"
<after_member_name(2)>
:
<before_member_value(Boolean, 2)>
true
<after_member_value(Boolean, 2)>

<end_object(2, false)>
}
<after_array_item(Object, 1)>
,
<before_array_item(Object, 1)>
{
<begin_object(2)>

<before_member_name(2)>
"first"
<after_member_name(2)>
:
<before_member_value(Boolean, 2)>
false
<after_member_value(Boolean, 2)>
,
<before_member_name(2)>
"second"
<after_member_name(2)>
:
<before_member_value(Number, 2)>
12
<after_member_value(Number, 2)>

<end_object(2, false)>
}
<after_array_item(Object, 1)>

<end_array(1, false)>
]
<after_top_level_value(Array)>
#
<before_top_level_value(Object)>
{
<begin_object(1)>

<before_member_name(1)>
"name"
<after_member_name(1)>
:
<before_member_value(Number, 1)>
123
<after_member_value(Number, 1)>

<end_object(1, false)>
}
<after_top_level_value(Object)>
"#,
        json
    );
    Ok(())
}

/// Tests writing not only whitespace but also ANSI escape codes
///
/// This is not valid JSON since the specification only permits whitespace between values.
/// However, when displaying the data only on console that is not an issue, see
/// <https://github.com/Marcono1234/struson/issues/105> for a use case.
///
/// Support for this is intentionally not mentioned in the Struson API, but this test
/// here verifies that the implementation does not reject this.
///
/// Note: Only ANSI escape codes might be safe for this purpose because the JSON specification
/// requires that within JSON string values the control character must be escaped. Therefore
/// JSON string values containing the control character cannot break formatting.
/// Implementing any other kind of format (e.g. HTML) is discouraged because JSON string values
/// or member names could (intentionally) break it. For these use cases a custom JsonWriter
/// implementation might be better suited.
#[test]
fn colorizing_pretty_printer() -> Result<(), Box<dyn Error>> {
    struct ColorizingPrettyPrinter {
        custom_style_active: bool,
    }
    impl ColorizingPrettyPrinter {
        fn start_color(
            &mut self,
            value_type: ValueType,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            // Write ANSI escape code, see https://en.wikipedia.org/wiki/ANSI_escape_code#Select_Graphic_Rendition_parameters
            write(b"\x1B[")?;
            write(
                match value_type {
                    ValueType::Array => "33",
                    ValueType::Object => "33",
                    ValueType::String => "34",
                    ValueType::Number => "94",
                    ValueType::Boolean => "95",
                    ValueType::Null => "96",
                }
                .as_bytes(),
            )?;
            write(b"m")?;

            if self.custom_style_active {
                write(b"\x1B[3m\x1B[4m")?;
                self.custom_style_active = false;
            }
            Ok(())
        }

        fn end_color(write: &mut impl FnMut(&[u8]) -> Result<(), IoError>) -> Result<(), IoError> {
            // Reset color
            write(b"\x1B[0m")
        }
    }
    impl PrettyPrinter for ColorizingPrettyPrinter {
        fn begin_array(
            &mut self,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            SimplePrettyPrinter.begin_array(nesting_depth, write)?;
            // End color of the opening `[`
            Self::end_color(write)
        }

        fn end_array(
            &mut self,
            nesting_depth: u32,
            is_empty: bool,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            SimplePrettyPrinter.end_array(nesting_depth, is_empty, write)?;
            // Colorize closing `]`
            self.start_color(ValueType::Array, write)
        }

        fn begin_object(
            &mut self,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            SimplePrettyPrinter.begin_object(nesting_depth, write)?;
            // End color of the opening `{`
            Self::end_color(write)
        }

        fn end_object(
            &mut self,
            nesting_depth: u32,
            is_empty: bool,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            SimplePrettyPrinter.end_object(nesting_depth, is_empty, write)?;
            // Colorize closing `}`
            self.start_color(ValueType::Object, write)
        }

        fn before_top_level_value(
            &mut self,
            value_type: ValueType,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            SimplePrettyPrinter.before_top_level_value(value_type, write)?;
            self.start_color(value_type, write)
        }

        fn after_top_level_value(
            &mut self,
            value_type: ValueType,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            SimplePrettyPrinter.after_top_level_value(value_type, write)?;
            Self::end_color(write)
        }

        fn before_array_item(
            &mut self,
            value_type: struson::reader::ValueType,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            SimplePrettyPrinter.before_array_item(value_type, nesting_depth, write)?;
            self.start_color(value_type, write)
        }

        fn after_array_item(
            &mut self,
            value_type: struson::reader::ValueType,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            SimplePrettyPrinter.after_array_item(value_type, nesting_depth, write)?;
            Self::end_color(write)
        }

        fn before_member_name(
            &mut self,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            SimplePrettyPrinter.before_member_name(nesting_depth, write)?;
            self.start_color(ValueType::String, write)
        }

        fn after_member_name(
            &mut self,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            SimplePrettyPrinter.after_member_name(nesting_depth, write)?;
            Self::end_color(write)
        }

        fn before_member_value(
            &mut self,
            value_type: struson::reader::ValueType,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            SimplePrettyPrinter.before_member_value(value_type, nesting_depth, write)?;
            self.start_color(value_type, write)
        }

        fn after_member_value(
            &mut self,
            value_type: struson::reader::ValueType,
            nesting_depth: u32,
            write: &mut impl FnMut(&[u8]) -> Result<(), IoError>,
        ) -> Result<(), IoError> {
            SimplePrettyPrinter.after_member_value(value_type, nesting_depth, write)?;
            Self::end_color(write)
        }
    }

    let mut writer = Vec::<u8>::new();
    let mut json_writer = JsonStreamWriter::new_custom(
        &mut writer,
        WriterSettings::default(),
        ColorizingPrettyPrinter {
            custom_style_active: false,
        },
    );

    json_writer.begin_array()?;
    json_writer.bool_value(true)?;
    json_writer.string_value("value")?;

    json_writer.begin_object()?;

    json_writer.name("name")?;
    json_writer.number_value(123)?;

    json_writer.name("normal")?;
    json_writer.null_value()?;

    json_writer.name("special")?;
    json_writer.pretty_printer().custom_style_active = true;
    json_writer.null_value()?;

    json_writer.end_object()?;
    json_writer.end_array()?;
    json_writer.finish_document()?;

    let json = String::from_utf8(writer)?;
    assert_eq!(
        "\u{1b}[33m[\u{1b}[0m
  \u{1b}[95mtrue\u{1b}[0m,
  \u{1b}[34m\"value\"\u{1b}[0m,
  \u{1b}[33m{\u{1b}[0m
    \u{1b}[34m\"name\"\u{1b}[0m: \u{1b}[94m123\u{1b}[0m,
    \u{1b}[34m\"normal\"\u{1b}[0m: \u{1b}[96mnull\u{1b}[0m,
    \u{1b}[34m\"special\"\u{1b}[0m: \u{1b}[96m\u{1b}[3m\u{1b}[4mnull\u{1b}[0m
  \u{1b}[33m}\u{1b}[0m
\u{1b}[33m]\u{1b}[0m",
        json
    );
    Ok(())
}
