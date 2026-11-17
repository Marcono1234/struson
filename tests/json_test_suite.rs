use std::{
    collections::HashMap,
    env,
    error::Error,
    fs,
    io::Cursor,
    path::{Path, PathBuf},
};

use serde::Deserialize;
use struson::reader::{JsonReader, JsonStreamReader};

#[derive(Debug, Deserialize, PartialEq)]
#[serde(rename_all = "lowercase")]
enum Expect {
    Accept,
    Reject,
    Any,
}

#[derive(Clone, Copy, Debug, Deserialize, PartialEq)]
enum InputEncoding {
    #[serde(rename = "utf-8")]
    Utf8,
    #[serde(rename = "hex")]
    Hex,
}

#[derive(Debug, Deserialize)]
struct TestCase {
    id: String,
    input: String,
    input_encoding: InputEncoding,
    expect: Expect,
    #[serde(default)]
    decoded: Option<serde_json::Value>,
}

#[derive(Debug, Deserialize)]
struct TestSuite {
    cases: Vec<TestCase>,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Decision {
    Accept,
    Reject,
}

// These are deliberate Struson behavior choices for the upstream "any" cases.
// Number values are accepted because skip_value validates number syntax without converting
// to a bounded numeric type (src/reader/mod.rs:1560-1565, src/reader/stream_reader.rs:1946-1988).
// Duplicate names are accepted by default (src/reader/mod.rs:1278-1282).
// Unpaired surrogates and non-UTF-8 data are rejected (src/reader/mod.rs:588-594, 781-785;
// src/reader/stream_reader.rs:102-104).
// A leading BOM is rejected (src/reader/stream_reader.rs:102-104, 4855-4864).
// 500 nested arrays are rejected by the default nesting limit of 128
// (src/reader/stream_reader.rs:402-414).
const ANY_CASE_DECISIONS: &[(&str, Decision)] = &[
    ("jts-8259-i_number_double_huge_neg_exp", Decision::Accept),
    ("jts-8259-i_number_huge_exp", Decision::Accept),
    ("jts-8259-i_number_neg_int_huge_exp", Decision::Accept),
    ("jts-8259-i_number_pos_double_huge_exp", Decision::Accept),
    ("jts-8259-i_number_real_neg_overflow", Decision::Accept),
    ("jts-8259-i_number_real_pos_overflow", Decision::Accept),
    ("jts-8259-i_number_real_underflow", Decision::Accept),
    ("jts-8259-i_number_too_big_neg_int", Decision::Accept),
    ("jts-8259-i_number_too_big_pos_int", Decision::Accept),
    ("jts-8259-i_number_very_big_negative_int", Decision::Accept),
    ("jts-8259-i_object_key_lone_2nd_surrogate", Decision::Reject),
    (
        "jts-8259-i_string_1st_surrogate_but_2nd_missing",
        Decision::Reject,
    ),
    (
        "jts-8259-i_string_1st_valid_surrogate_2nd_invalid",
        Decision::Reject,
    ),
    ("jts-8259-i_string_UTF-16LE_with_BOM", Decision::Reject),
    ("jts-8259-i_string_UTF-8_invalid_sequence", Decision::Reject),
    ("jts-8259-i_string_UTF8_surrogate_U+D800", Decision::Reject),
    (
        "jts-8259-i_string_incomplete_surrogate_and_escape_valid",
        Decision::Reject,
    ),
    (
        "jts-8259-i_string_incomplete_surrogate_pair",
        Decision::Reject,
    ),
    (
        "jts-8259-i_string_incomplete_surrogates_escape_valid",
        Decision::Reject,
    ),
    (
        "jts-8259-i_string_invalid_lonely_surrogate",
        Decision::Reject,
    ),
    ("jts-8259-i_string_invalid_surrogate", Decision::Reject),
    ("jts-8259-i_string_invalid_utf-8", Decision::Reject),
    (
        "jts-8259-i_string_inverted_surrogates_U+1D11E",
        Decision::Reject,
    ),
    ("jts-8259-i_string_iso_latin_1", Decision::Reject),
    ("jts-8259-i_string_lone_second_surrogate", Decision::Reject),
    (
        "jts-8259-i_string_lone_utf8_continuation_byte",
        Decision::Reject,
    ),
    ("jts-8259-i_string_not_in_unicode_range", Decision::Reject),
    (
        "jts-8259-i_string_overlong_sequence_2_bytes",
        Decision::Reject,
    ),
    (
        "jts-8259-i_string_overlong_sequence_6_bytes",
        Decision::Reject,
    ),
    (
        "jts-8259-i_string_overlong_sequence_6_bytes_null",
        Decision::Reject,
    ),
    ("jts-8259-i_string_truncated-utf-8", Decision::Reject),
    ("jts-8259-i_string_utf16BE_no_BOM", Decision::Reject),
    ("jts-8259-i_string_utf16LE_no_BOM", Decision::Reject),
    ("jts-8259-i_structure_500_nested_arrays", Decision::Reject),
    (
        "jts-8259-i_structure_UTF-8_BOM_empty_object",
        Decision::Reject,
    ),
    ("jts-8259-y_object_duplicated_key", Decision::Accept),
    (
        "jts-8259-y_object_duplicated_key_and_value",
        Decision::Accept,
    ),
    ("json-8259-duplicate-keys", Decision::Accept),
];

fn parse_document(input: &[u8]) -> Result<(), Box<dyn Error>> {
    let mut reader = JsonStreamReader::new(Cursor::new(input));
    reader.skip_value()?;
    reader.consume_trailing_whitespace()?;
    Ok(())
}

#[cfg(feature = "serde")]
fn parse_value_document(input: &[u8]) -> Result<serde_json::Value, Box<dyn Error>> {
    let mut reader = JsonStreamReader::new(Cursor::new(input));
    let value = reader.deserialize_next::<serde_json::Value>()?;
    reader.consume_trailing_whitespace()?;
    Ok(value)
}

fn decode_hex(input: &str) -> Result<Vec<u8>, String> {
    if !input.len().is_multiple_of(2) {
        return Err("hex input has an odd number of digits".to_owned());
    }

    let bytes = input.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len() / 2);
    for index in (0..bytes.len()).step_by(2) {
        let pair = std::str::from_utf8(&bytes[index..index + 2])
            .map_err(|_| format!("hex input has non-ASCII data at byte {index}"))?;
        if !pair.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(format!("hex input has a non-hex digit at byte {index}"));
        }
        decoded.push(
            u8::from_str_radix(pair, 16)
                .map_err(|_| format!("invalid hex byte at byte {index}"))?,
        );
    }
    Ok(decoded)
}

fn case_input(case: &TestCase) -> Vec<u8> {
    match case.input_encoding {
        InputEncoding::Utf8 => case.input.as_bytes().to_vec(),
        InputEncoding::Hex => decode_hex(&case.input)
            .unwrap_or_else(|error| panic!("invalid hex input for {}: {error}", case.id)),
    }
}

#[test]
fn rfc8259_test_suite() -> Result<(), Box<dyn Error>> {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/GLD.SerializerBenchmark/rfc8259.json");
    let suite: TestSuite = serde_json::from_slice(&fs::read(path)?)?;

    let mut decisions = HashMap::new();
    for &(id, decision) in ANY_CASE_DECISIONS {
        assert!(
            decisions.insert(id, decision).is_none(),
            "any-case decision list contains duplicate id {id}"
        );
    }

    let mut cases_by_id = HashMap::new();
    for case in &suite.cases {
        assert!(
            cases_by_id.insert(case.id.as_str(), case).is_none(),
            "GLD.SerializerBenchmark contains duplicate case id {}",
            case.id
        );
    }

    for &(id, _) in ANY_CASE_DECISIONS {
        let case = cases_by_id
            .get(id)
            .unwrap_or_else(|| panic!("any-case decision names unknown case id {id}"));
        assert_eq!(
            case.expect,
            Expect::Any,
            "any-case decision names non-any case id {id}"
        );
    }

    let any_case_count = suite
        .cases
        .iter()
        .filter(|case| case.expect == Expect::Any)
        .count();
    assert_eq!(
        decisions.len(),
        any_case_count,
        "every expect:any case must have exactly one explicit decision"
    );

    for case in &suite.cases {
        let input = case_input(case);
        let decision = match case.expect {
            Expect::Accept => Decision::Accept,
            Expect::Reject => Decision::Reject,
            Expect::Any => *decisions
                .get(case.id.as_str())
                .unwrap_or_else(|| panic!("missing decision for expect:any case {}", case.id)),
        };

        match (decision, parse_document(&input)) {
            (Decision::Accept, Ok(())) | (Decision::Reject, Err(_)) => {}
            (Decision::Accept, Err(error)) => {
                panic!(
                    "case {} should be accepted but was rejected: {error}",
                    case.id
                )
            }
            (Decision::Reject, Ok(())) => {
                panic!("case {} should be rejected but was accepted", case.id)
            }
        }

        if case.decoded.is_some() {
            assert_eq!(
                decision,
                Decision::Accept,
                "case {} has decoded data but is configured as rejected",
                case.id
            );
        }

        #[cfg(feature = "serde")]
        if let Some(decoded) = case.decoded.as_ref() {
            let actual = parse_value_document(&input).unwrap_or_else(|error| {
                panic!(
                    "case {} was accepted by skip_value but failed value deserialization: {error}",
                    case.id
                )
            });
            assert_eq!(
                &actual, decoded,
                "decoded value mismatch for case {}",
                case.id
            );
        }
    }

    Ok(())
}

#[expect(unused, reason = "manual helper script; run as dummy 'test'")]
// #[test]
fn shrink_test_file() -> Result<(), Box<dyn Error>> {
    // Read a local pinned checkout instead of downloading from a moving branch so generation stays offline and repeatable.
    let source = env::var_os("GLD_RFC8259_SOURCE")
        .ok_or("set GLD_RFC8259_SOURCE to the local upstream rfc8259.json path")?;
    let mut suite: serde_json::Value = serde_json::from_slice(&fs::read(PathBuf::from(source))?)?;
    let cases = suite
        .get_mut("cases")
        .and_then(serde_json::Value::as_array_mut)
        .ok_or("upstream rfc8259.json has no cases array")?;

    let retained_fields = ["id", "input", "input_encoding", "expect", "decoded"];
    for case in cases {
        let case = case
            .as_object_mut()
            .ok_or("upstream case is not a JSON object")?;
        case.retain(|name, _| retained_fields.contains(&name.as_str()));
    }

    let output_path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/GLD.SerializerBenchmark/rfc8259.json");
    fs::write(
        output_path,
        format!("{}\n", serde_json::to_string_pretty(&suite)?),
    )?;
    Ok(())
}
