#![cfg(feature = "serde")]

use std::{collections::HashMap, fmt::Debug};

use serde::{de::DeserializeOwned, Deserialize};
use struson::{
    reader::{JsonReader, JsonStreamReader, ReaderError, UnexpectedStructureKind, ValueType},
    serde::{DeserializerError, JsonReaderDeserializer},
};

fn assert_deserialized<D: DeserializeOwned + PartialEq + Debug>(
    json: &str,
    expected_deserialized: D,
) {
    let mut json_reader = JsonStreamReader::new(json.as_bytes());
    let mut deserializer = JsonReaderDeserializer::new(&mut json_reader);
    let value = D::deserialize(&mut deserializer).unwrap();
    json_reader.consume_trailing_whitespace().unwrap();
    assert_eq!(expected_deserialized, value);

    let value_serde_json = serde_json::from_str(json).unwrap();
    assert_eq!(
        expected_deserialized, value_serde_json,
        "Serde JSON deserialized value does not match expected value"
    );
}

macro_rules! assert_deserialize_error {
    ($json:expr, $type:ident, $expected_pattern:pat_param => $assertion:expr, $serde_error:ident => $assertion_serde:expr) => {
        let mut json_reader = JsonStreamReader::new($json.as_bytes());
        let mut deserializer = JsonReaderDeserializer::new(&mut json_reader);
        match $type::deserialize(&mut deserializer) {
            Err($expected_pattern) => $assertion,
            r => panic!("Unexpected result for '{}': {r:?}", $json),
        }

        match serde_json::from_str::<$type>($json) {
            Err($serde_error) => $assertion_serde,
            r => panic!("Unexpected result for Serde JSON for '{}': {r:?}", $json),
        }
    };
}

#[test]
fn deserialize_enum() {
    #[derive(Deserialize, PartialEq, Debug)]
    enum E {
        A,              // unit
        B(u8),          // newtype
        C(i16, String), // tuple
        D {
            // struct
            a: f32,
            b: Vec<bool>,
        },
    }

    assert_deserialized("\"A\"", E::A);
    assert_deserialized(r#"{"A": null}"#, E::A);

    assert_deserialized(r#"{"B": 5}"#, E::B(5));
    assert_deserialize_error!(
        "\"B\"",
        E,
        DeserializerError::Custom(message) => assert_eq!("invalid type: unit variant, expected newtype variant", message),
        serde_error => assert_eq!("invalid type: unit variant, expected newtype variant", serde_error.to_string())
    );

    assert_deserialized(r#"{"C": [-7, "test"]}"#, E::C(-7, "test".to_owned()));
    assert_deserialize_error!(
        r#"{"C": 5}"#,
        E,
        DeserializerError::ReaderError(ReaderError::UnexpectedValueType { expected, actual, .. }) => {
            assert_eq!(ValueType::Array, expected);
            assert_eq!(ValueType::Number, actual);
        },
        serde_error => assert_eq!("invalid type: integer `5`, expected tuple variant E::C at line 1 column 7", serde_error.to_string())
    );

    assert_deserialized(
        r#"{"D": {"a": 1.5, "b": [true]}}"#,
        E::D {
            a: 1.5,
            b: vec![true],
        },
    );
    assert_deserialized(
        r#"{"D": [3.2, [false]]}"#,
        E::D {
            a: 3.2,
            b: vec![false],
        },
    );
    assert_deserialize_error!(
        r#"{"D": 1.2}"#,
        E,
        DeserializerError::Custom(message) => assert_eq!("invalid type: number, expected struct variant E::D", message),
        serde_error => assert_eq!("invalid type: floating point `1.2`, expected struct variant E::D at line 1 column 9", serde_error.to_string())
    );

    assert_deserialize_error!(
        r#"{"E": 1}"#,
        E,
        DeserializerError::Custom(message) => assert_eq!("unknown variant `E`, expected one of `A`, `B`, `C`, `D`", message),
        serde_error => assert_eq!("unknown variant `E`, expected one of `A`, `B`, `C`, `D` at line 1 column 4", serde_error.to_string())
    );
}

#[test]
fn deserialize_map() {
    assert_deserialized("{}", HashMap::<String, u8>::new());
    assert_deserialized(r#"{"": 1}"#, HashMap::from([("".to_owned(), 1)]));
    assert_deserialized(r#"{"a": 1}"#, HashMap::from([("a".to_owned(), 1)]));
    assert_deserialized(
        r#"{"1": true, "2": false}"#,
        HashMap::from([(1, true), (2, false)]),
    );
    assert_deserialized(
        r#"{"a": [1, 2], "b": [3, 4]}"#,
        HashMap::from([("a".to_owned(), vec![1, 2]), ("b".to_owned(), vec![3, 4])]),
    );

    // Duplicate key
    assert_deserialized(r#"{"a": 1, "a": 2}"#, HashMap::from([("a".to_owned(), 2)]));
}

#[test]
fn deserialize_unit_struct() {
    #[derive(Deserialize, PartialEq, Debug)]
    struct S;

    assert_deserialized("null", S);
}

#[test]
fn deserialize_newtype_struct() {
    #[derive(Deserialize, PartialEq, Debug)]
    struct S(u8);

    assert_deserialized("5", S(5));
}

#[test]
fn deserialize_tuple_struct() {
    #[derive(Deserialize, PartialEq, Debug)]
    struct S(u8, String);

    assert_deserialized("[8, \"test\"]", S(8, "test".to_owned()));

    assert_deserialize_error!(
        "[1]",
        S,
        DeserializerError::Custom(message) => assert_eq!("invalid length 1, expected tuple struct S with 2 elements", message),
        serde_error => assert_eq!("invalid length 1, expected tuple struct S with 2 elements at line 1 column 3", serde_error.to_string())
    );
    assert_deserialize_error!(
        "[1, \"test\", 2]",
        S,
        DeserializerError::ReaderError(ReaderError::UnexpectedStructure { kind, .. }) => assert_eq!(UnexpectedStructureKind::MoreElementsThanExpected, kind),
        serde_error => assert_eq!("trailing characters at line 1 column 13", serde_error.to_string())
    );
}

#[test]
fn deserialize_struct() {
    #[derive(Deserialize, PartialEq, Debug)]
    struct S {
        a: f32,
        b: Vec<bool>,
    }

    assert_deserialized(
        r#"{"a": 4.1, "b": [false]}"#,
        S {
            a: 4.1,
            b: vec![false],
        },
    );
    assert_deserialized(
        "[1.2, [true]]",
        S {
            a: 1.2,
            b: vec![true],
        },
    );

    assert_deserialize_error!(
        r#"{"a": 1, "a": 2}"#,
        S,
        DeserializerError::Custom(message) => assert_eq!("duplicate field `a`", message),
        serde_error => assert_eq!("duplicate field `a` at line 1 column 12", serde_error.to_string())
    );

    assert_deserialize_error!(
        "[1]",
        S,
        DeserializerError::Custom(message) => assert_eq!("invalid length 1, expected struct S with 2 elements", message),
        serde_error => assert_eq!("invalid length 1, expected struct S with 2 elements at line 1 column 3", serde_error.to_string())
    );
    assert_deserialize_error!(
        "[1, [true], false]",
        S,
        DeserializerError::ReaderError(ReaderError::UnexpectedStructure { kind, .. }) => assert_eq!(UnexpectedStructureKind::MoreElementsThanExpected, kind),
        serde_error => assert_eq!("trailing characters at line 1 column 13", serde_error.to_string())
    );
}

#[test]
fn deserialize_option() {
    assert_deserialized("5", Some(5));
    assert_deserialized("null", None::<i64>);

    // Ambiguity for values which are themselves serialized as `null`
    assert_deserialized("null", None::<()>);
}

#[test]
fn deserialize_seq() {
    assert_deserialized("[]", Vec::<u8>::new());
    assert_deserialized("[null]", vec![()]);
    assert_deserialized("[1, -3, 4.5]", vec![1.0, -3.0, 4.5]);
}

#[test]
fn deserialize_string() {
    assert_deserialized(
        "\"a \\u0000 \\uD852\\uDF62 \u{10FFFF}\"",
        "a \0 \u{24B62} \u{10FFFF}".to_owned(),
    );
}
