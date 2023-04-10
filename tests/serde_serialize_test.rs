#![cfg(feature = "serde")]

use std::collections::{BTreeMap, HashMap};

use serde::Serialize;
use struson::{
    serde::JsonWriterSerializer,
    writer::{JsonStreamWriter, JsonWriter},
};

fn assert_serialized<S: Serialize>(s: S, expected_json: &str) {
    let mut writer = Vec::<u8>::new();
    let mut json_writer = JsonStreamWriter::new(&mut writer);
    let mut serializer = JsonWriterSerializer::new(&mut json_writer);
    s.serialize(&mut serializer).unwrap();
    json_writer.finish_document().unwrap();
    let json = String::from_utf8(writer).unwrap();
    assert_eq!(expected_json, json);

    let serde_json = serde_json::to_string(&s).unwrap();
    assert_eq!(
        expected_json, serde_json,
        "Serde JSON output does not match expected JSON"
    );
}

#[test]
fn serialize_map() {
    // Use BTreeMap for consistent entry order
    assert_serialized(
        BTreeMap::from([("a", vec![1, 2]), ("b", vec![3, 4])]),
        r#"{"a":[1,2],"b":[3,4]}"#,
    );

    assert_serialized(HashMap::from([(1, 2)]), r#"{"1":2}"#);
}

#[test]
fn serialize_newtype_struct() {
    #[derive(Serialize)]
    struct S(Vec<u8>);

    assert_serialized(S(vec![1, 2]), "[1,2]");
}

#[test]
fn serialize_newtype_variant() {
    #[derive(Serialize)]
    enum E {
        A(Vec<u8>),
    }

    assert_serialized(E::A(vec![1, 2]), r#"{"A":[1,2]}"#);
}

#[test]
fn serialize_option() {
    assert_serialized(vec![None, Some(1)], "[null,1]");

    // Ambiguity for values which are themselves serialized as `null`
    assert_serialized(vec![None, Some(())], "[null,null]");
}

#[test]
fn serialize_struct() {
    #[derive(Serialize)]
    struct S {
        a: u64,
        b: bool,
        c: Vec<S>,
    }

    assert_serialized(
        S {
            a: 1,
            b: true,
            c: vec![S {
                a: 2,
                b: false,
                c: Vec::new(),
            }],
        },
        r#"{"a":1,"b":true,"c":[{"a":2,"b":false,"c":[]}]}"#,
    );
}

#[test]
fn serialize_struct_variant() {
    #[derive(Serialize)]
    enum E {
        A { a: i8, b: String },
    }

    assert_serialized(
        E::A {
            a: -3,
            b: "test".to_owned(),
        },
        r#"{"A":{"a":-3,"b":"test"}}"#,
    );
}

#[test]
fn serialize_tuple() {
    assert_serialized((true, 1, "test"), r#"[true,1,"test"]"#);
}

#[test]
fn serialize_tuple_struct() {
    #[derive(Serialize)]
    struct S(bool, Vec<u8>, &'static str);

    assert_serialized(S(true, vec![1], "test"), r#"[true,[1],"test"]"#);
}

#[test]
fn serialize_tuple_variant() {
    #[derive(Serialize)]
    enum E {
        A(bool, i8),
    }

    assert_serialized(E::A(true, -3), r#"{"A":[true,-3]}"#);
}

#[test]
fn serialize_unit() {
    assert_serialized((), "null");
}

#[test]
fn serialize_unit_struct() {
    #[derive(Serialize)]
    struct S;

    assert_serialized(S, "null");
}

#[test]
fn serialize_unit_variant() {
    #[derive(Serialize)]
    enum E {
        A,
    }

    assert_serialized(E::A, "\"A\"");
}
