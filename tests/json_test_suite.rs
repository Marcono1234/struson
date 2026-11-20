//! Runs a test suite checking for JSON RFC 8259 compliance

use std::{
    collections::HashMap,
    env,
    error::Error,
    fmt::Display,
    fs::File,
    io::{BufReader, BufWriter, Write},
    path::{Path, PathBuf},
    sync::LazyLock,
};

use struson::reader::{
    DuplicateNameDetection, JsonReader, JsonStreamReader, ReaderSettings, ValueType,
};
use test_suite::*;

/// Serde types representing the test suite data
mod test_suite {
    use serde::Deserialize;

    #[derive(Debug, Deserialize, PartialEq)]
    #[serde(rename_all = "lowercase")]
    pub enum Expect {
        Accept,
        Reject,
        /// JSON libraries may accept or reject the input; see [`super::ANY_CASE_DECISIONS`]
        /// for expected Struson behavior
        Any,
    }

    #[derive(Clone, Copy, Debug, Deserialize, PartialEq)]
    pub enum InputEncoding {
        #[serde(rename = "utf-8")]
        Utf8,
        #[serde(rename = "hex")]
        Hex,
    }

    #[derive(Debug, Deserialize)]
    pub struct TestCase {
        pub id: String,
        pub input: String,
        pub input_encoding: InputEncoding,
        pub expect: Expect,
        pub decoded: Option<serde_json::Value>,
    }

    #[derive(Debug, Deserialize)]
    pub struct TestSuite {
        pub cases: Vec<TestCase>,
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Decision {
    Accept,
    Reject,
}

type ConditionFunction = dyn (Fn(
        &ReaderSettings,
        // TODO(rust): Add name for this parameter, needs https://github.com/rust-lang/rust/issues/158499
        /* is_skip: */
        bool,
    ) -> Decision)
    // these traits are needed to support storing this function in `static` variable
    + Sync
    + Send;

/// Decision for an 'i' (`expect: any`) test case
enum IDecision {
    Accept,
    Reject,
    /// Decision depends on reader settings and which reader API is used
    Conditional(Box<ConditionFunction>),
}
impl IDecision {
    /// How to handle large numbers
    fn large_number() -> Self {
        IDecision::Conditional(Box::new(|settings, is_skip| {
            if settings.restrict_number_values && !is_skip {
                Decision::Reject
            } else {
                Decision::Accept
            }
        }))
    }

    /// How to handle deeply nested JSON data
    fn deep_nesting() -> Self {
        IDecision::Conditional(Box::new(|settings, _is_skip| {
            match settings.max_nesting_depth {
                Some(_) => Decision::Reject,
                None => Decision::Accept,
            }
        }))
    }

    /// How to handle duplicate names
    fn duplicate_name() -> Self {
        IDecision::Conditional(Box::new(|settings, is_skip| {
            match settings.duplicate_name_detection {
                DuplicateNameDetection::Disabled => Decision::Accept,
                // `ReadNames` does not check for duplicates when skipping
                DuplicateNameDetection::ReadNames if is_skip => Decision::Accept,
                _ => Decision::Reject,
            }
        }))
    }

    fn decide(&self, settings: &ReaderSettings, is_skip: bool) -> Decision {
        match self {
            IDecision::Accept => Decision::Accept,
            IDecision::Reject => Decision::Reject,
            IDecision::Conditional(condition) => condition(settings, is_skip),
        }
    }
}

static TEST_SUITE_PATH: LazyLock<PathBuf> = LazyLock::new(|| {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/GLD.SerializerBenchmark-json-test-suite/rfc8259.json")
});

/// Deliberate Struson behavior choices for the upstream `expect: any` cases
static ANY_CASE_DECISIONS: LazyLock<HashMap<&str, IDecision>> = LazyLock::new(|| {
    let entries = [
        // For large numbers decide based on reader settings
        (
            "jts-8259-i_number_double_huge_neg_exp",
            IDecision::large_number(),
        ),
        ("jts-8259-i_number_huge_exp", IDecision::large_number()),
        (
            "jts-8259-i_number_neg_int_huge_exp",
            IDecision::large_number(),
        ),
        (
            "jts-8259-i_number_pos_double_huge_exp",
            IDecision::large_number(),
        ),
        (
            "jts-8259-i_number_real_neg_overflow",
            IDecision::large_number(),
        ),
        (
            "jts-8259-i_number_real_pos_overflow",
            IDecision::large_number(),
        ),
        (
            "jts-8259-i_number_real_underflow",
            IDecision::large_number(),
        ),
        // Accept large integer numbers (at least these ones which are still within Struson's limit)
        ("jts-8259-i_number_too_big_neg_int", IDecision::Accept),
        ("jts-8259-i_number_too_big_pos_int", IDecision::Accept),
        ("jts-8259-i_number_very_big_negative_int", IDecision::Accept),
        // Reject malformed UTF-8
        (
            "jts-8259-i_object_key_lone_2nd_surrogate",
            IDecision::Reject,
        ),
        (
            "jts-8259-i_string_1st_surrogate_but_2nd_missing",
            IDecision::Reject,
        ),
        (
            "jts-8259-i_string_1st_valid_surrogate_2nd_invalid",
            IDecision::Reject,
        ),
        (
            "jts-8259-i_string_incomplete_surrogate_and_escape_valid",
            IDecision::Reject,
        ),
        (
            "jts-8259-i_string_incomplete_surrogate_pair",
            IDecision::Reject,
        ),
        (
            "jts-8259-i_string_incomplete_surrogates_escape_valid",
            IDecision::Reject,
        ),
        (
            "jts-8259-i_string_invalid_lonely_surrogate",
            IDecision::Reject,
        ),
        ("jts-8259-i_string_invalid_surrogate", IDecision::Reject),
        (
            "jts-8259-i_string_inverted_surrogates_U+1D11E",
            IDecision::Reject,
        ),
        ("jts-8259-i_string_lone_second_surrogate", IDecision::Reject),
        ("json-8259-lone-surrogate", IDecision::Reject),
        (
            "jts-8259-i_structure_UTF-8_BOM_empty_object",
            IDecision::Reject,
        ),
        // For deeply nested JSON decide based on reader settings
        (
            "jts-8259-i_structure_500_nested_arrays",
            IDecision::deep_nesting(),
        ),
        // For duplicate names decide based on reader settings
        (
            "jts-8259-y_object_duplicated_key",
            IDecision::duplicate_name(),
        ),
        (
            "jts-8259-y_object_duplicated_key_and_value",
            IDecision::duplicate_name(),
        ),
        ("json-8259-duplicate-keys", IDecision::duplicate_name()),
    ];

    let mut map = HashMap::with_capacity(entries.len());
    // Note: Don't use `HashMap::from` because it does not report an error on duplicate keys
    for (id, decision) in entries {
        assert!(
            map.insert(id, decision).is_none(),
            "[test-setup-error] any-case decision list contains duplicate id {id}"
        );
    }
    map
});

/// Executes most of [`JsonStreamReader`]'s reading methods
fn execute_read(input: &[u8], settings: ReaderSettings) -> Result<(), Box<dyn Error>> {
    let mut json_reader = JsonStreamReader::new_custom(input, settings);

    #[derive(Debug)]
    enum StackValue {
        Array,
        Object,
    }

    let mut stack = Vec::new();
    loop {
        if !stack.is_empty() {
            match stack.last().unwrap() {
                StackValue::Array => {
                    if !json_reader.has_next()? {
                        stack.pop();
                        json_reader.end_array()?;

                        if stack.is_empty() {
                            break;
                        } else {
                            continue;
                        }
                    }
                }
                StackValue::Object => {
                    if json_reader.has_next()? {
                        json_reader.next_name()?;
                        // fall through to value reading
                    } else {
                        stack.pop();
                        json_reader.end_object()?;

                        if stack.is_empty() {
                            break;
                        } else {
                            continue;
                        }
                    }
                }
            }
        }

        match json_reader.peek()? {
            ValueType::Array => {
                json_reader.begin_array()?;
                stack.push(StackValue::Array)
            }
            ValueType::Object => {
                json_reader.begin_object()?;
                stack.push(StackValue::Object)
            }
            ValueType::String => {
                json_reader.next_str()?;
            }
            ValueType::Number => {
                json_reader.next_number_as_str()?;
            }
            ValueType::Boolean => {
                json_reader.next_bool()?;
            }
            ValueType::Null => json_reader.next_null()?,
        }

        if stack.is_empty() {
            break;
        }
    }
    json_reader.consume_trailing_whitespace()?;
    Ok(())
}

/// Executes [`JsonStreamReader::skip_value`]
fn execute_skip(input: &[u8], settings: ReaderSettings) -> Result<(), Box<dyn Error>> {
    let mut json_reader = JsonStreamReader::new_custom(input, settings);
    json_reader.skip_value()?;
    json_reader.consume_trailing_whitespace()?;
    Ok(())
}

/// Executes [`JsonStreamReader::deserialize_next`]
#[cfg(feature = "serde")]
fn execute_deserialize(
    input: &[u8],
    settings: ReaderSettings,
) -> Result<serde_json::Value, Box<dyn Error>> {
    let mut reader = JsonStreamReader::new_custom(input, settings);
    let value = reader.deserialize_next::<serde_json::Value>()?;
    reader.consume_trailing_whitespace()?;
    Ok(value)
}

/// Gets the JSON data for [`TestCase::input`]
fn case_input(case: &TestCase) -> Vec<u8> {
    fn decode_hex(input: &str) -> Result<Vec<u8>, String> {
        if !input.len().is_multiple_of(2) {
            return Err("hex input has an odd number of digits".to_owned());
        }

        (0..input.len())
            // `u8` is represented by two hex chars
            .step_by(2)
            .map(|index| {
                u8::from_str_radix(&input[index..index + 2], 16)
                    .map_err(|_| format!("invalid hex byte at index {index}"))
            })
            .collect()
    }
    // Sanity check to make sure hex decoding works correctly
    debug_assert_eq!(
        decode_hex("0123456789abcdef").unwrap(),
        &[1, 35, 69, 103, 137, 171, 205, 239]
    );

    match case.input_encoding {
        InputEncoding::Utf8 => case.input.as_bytes().to_vec(),
        InputEncoding::Hex => decode_hex(&case.input).unwrap_or_else(|error| {
            let case_id = case.id.as_str();
            panic!("[test-setup-error] invalid hex input for {case_id}: {error}")
        }),
    }
}

#[test]
// Note: Don't return `Result` here to avoid accidentally using `?` for test call, which
// would then in case of failure be missing context (e.g. case id)
fn rfc8259_test_suite() {
    let suite: TestSuite =
        serde_json::from_reader(BufReader::new(File::open(&*TEST_SUITE_PATH).unwrap())).unwrap();

    let mut cases_by_id = HashMap::new();
    for case in &suite.cases {
        let case_id = case.id.as_str();
        assert!(
            cases_by_id.insert(case_id, case).is_none(),
            "[test-setup-error] test suite contains duplicate case id {}",
            case_id
        );
    }

    for id in ANY_CASE_DECISIONS.keys() {
        let case = cases_by_id.get(id).unwrap_or_else(|| {
            panic!("[test-setup-error] any-case decision names unknown case id {id}")
        });
        assert_eq!(
            case.expect,
            Expect::Any,
            "[test-setup-error] any-case decision names non-any-case id {id}"
        );
    }

    let reader_settings = [
        ("default", ReaderSettings::default()),
        (
            "additional-restrictions",
            ReaderSettings {
                duplicate_name_detection: DuplicateNameDetection::AllNames,
                ..Default::default()
            },
        ),
        (
            "no-restrictions",
            ReaderSettings {
                max_nesting_depth: None,
                restrict_number_values: false,
                ..Default::default()
            },
        ),
    ];

    #[derive(Clone, Copy, Debug, PartialEq)]
    enum TestKind {
        Read,
        Skip,
    }
    impl Display for TestKind {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let s = match self {
                Self::Read => "read",
                Self::Skip => "skip",
            };
            write!(f, "{s}")
        }
    }

    for (settings_kind, settings) in reader_settings {
        for case in &suite.cases {
            let case_id = case.id.as_str();
            let input = case_input(case);

            let decide = |is_skip: bool| match case.expect {
                Expect::Accept => Decision::Accept,
                Expect::Reject => Decision::Reject,
                Expect::Any => ANY_CASE_DECISIONS
                    .get(case_id)
                    .unwrap_or_else(|| {
                        panic!("[test-setup-error] missing decision for any-case {case_id}")
                    })
                    .decide(&settings, is_skip),
            };

            let check_result = |test_kind: TestKind, result: Result<(), Box<dyn Error>>| {
                let decision = decide(test_kind == TestKind::Skip);
                match (decision, result) {
                    (Decision::Accept, Ok(())) | (Decision::Reject, Err(_)) => {}
                    (Decision::Accept, Err(error)) => {
                        panic!(
                            "{settings_kind}:{test_kind}: case {case_id} should be accepted but was rejected: {error}"
                        )
                    }
                    (Decision::Reject, Ok(())) => {
                        panic!(
                            "{settings_kind}:{test_kind}: case {case_id} should be rejected but was accepted"
                        )
                    }
                }
            };

            check_result(TestKind::Read, execute_read(&input, settings.clone()));
            // Additionally test skipping value, because it has a separate implementation
            check_result(TestKind::Skip, execute_skip(&input, settings.clone()));

            if case.decoded.is_some() {
                let decision = decide(false);
                assert_eq!(
                    decision,
                    Decision::Accept,
                    "[test-setup-error] case {case_id} has decoded data but is configured as rejected"
                );
            }

            #[cfg(feature = "serde")]
            if let Some(decoded) = case.decoded.as_ref() {
                let actual = execute_deserialize(&input, settings.clone()).unwrap_or_else(|error| {
                    panic!(
                        "{settings_kind}: case {case_id} was parsed successfully but failed deserialization: {error}"
                    )
                });
                assert_eq!(
                    &actual, decoded,
                    "{settings_kind}: decoded value mismatch for case {case_id}"
                );
            }
        }
    }
}

/// Manual helper function for transforming the upstream `rfc8259.json` file,
/// keeping only the JSON members needed for running the test suite
///
/// See the [README](./GLD.SerializerBenchmark-json-test-suite/README.md) for how and
/// when to use this function.
#[expect(unused, reason = "manual helper function; run as dummy 'test'")]
// #[test]
fn shrink_test_file() -> Result<(), Box<dyn Error>> {
    fn upstream_file_path() -> PathBuf {
        // Create sibling file path with `-upstream` suffix in file name
        let mut file_name = TEST_SUITE_PATH.file_stem().unwrap().to_owned();
        file_name.push("-upstream");
        file_name.push(".");
        file_name.push(TEST_SUITE_PATH.extension().unwrap());
        TEST_SUITE_PATH.parent().unwrap().join(file_name)
    }

    let upstream_file_path = upstream_file_path();
    if !upstream_file_path.is_file() {
        return Err(format!(
            "upstream file does not exist: {}",
            upstream_file_path.display()
        )
        .into());
    }

    let mut suite: serde_json::Value =
        serde_json::from_reader(BufReader::new(File::open(&*upstream_file_path)?))?;
    let cases = suite
        .get_mut("cases")
        .and_then(serde_json::Value::as_array_mut)
        .ok_or("upstream suite file has no 'cases' array")?;

    // Keep only relevant fields to reduce test suite file size
    let retained_fields = ["id", "input", "input_encoding", "expect", "decoded"];
    for case in cases {
        let case = case
            .as_object_mut()
            .ok_or("upstream case is not a JSON object")?;
        case.retain(|name, _| retained_fields.contains(&name.as_str()));
    }

    let mut writer = BufWriter::new(File::create(&*TEST_SUITE_PATH)?);
    serde_json::to_writer_pretty(&mut writer, &suite)?;
    writer.write_all(b"\n")?;
    writer.flush()?;
    Ok(())
}
