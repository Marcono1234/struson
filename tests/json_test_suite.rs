use std::{
    error::Error,
    ffi::OsStr,
    fs,
    io::Cursor,
    path::{Path, PathBuf},
};

use struson::{
    reader::{JsonReader, JsonStreamReader},
    writer::JsonStreamWriter,
};

fn vector_paths(suite: &str) -> Result<Vec<PathBuf>, Box<dyn Error>> {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/JSONTestSuite")
        .join(suite);
    let mut paths = fs::read_dir(directory)?
        .map(|entry| entry.map(|entry| entry.path()))
        .collect::<Result<Vec<_>, _>>()?;
    paths.retain(|path| path.extension() == Some(OsStr::new("json")));
    paths.sort();
    Ok(paths)
}

fn parse_document(input: &[u8]) -> Result<(), Box<dyn Error>> {
    let mut reader = JsonStreamReader::new(Cursor::new(input));
    reader.skip_value()?;
    reader.consume_trailing_whitespace()?;
    Ok(())
}

fn transfer_document(input: &[u8]) -> Result<Vec<u8>, Box<dyn Error>> {
    let mut reader = JsonStreamReader::new(Cursor::new(input));
    let mut output = Vec::new();
    {
        let mut writer = JsonStreamWriter::new(&mut output);
        reader.transfer_to(&mut writer)?;
    }
    reader.consume_trailing_whitespace()?;
    Ok(output)
}

#[test]
fn json_test_suite() -> Result<(), Box<dyn Error>> {
    for suite in ["test_parsing", "test_transform"] {
        for path in vector_paths(suite)? {
            let file_name = path
                .file_name()
                .and_then(OsStr::to_str)
                .ok_or("JSONTestSuite file name is not valid UTF-8")?;
            let input = fs::read(&path)?;

            match suite {
                "test_parsing" => {
                    let result = parse_document(&input);
                    if file_name.starts_with("y_") {
                        result.unwrap_or_else(|error| {
                            panic!("valid JSONTestSuite case {file_name} was rejected: {error}")
                        });
                    } else if file_name.starts_with("n_") {
                        assert!(
                            result.is_err(),
                            "invalid JSONTestSuite case {file_name} was accepted"
                        );
                    } else if !file_name.starts_with("i_") {
                        panic!("unrecognized JSONTestSuite parsing case {file_name}");
                    }
                }
                "test_transform" => {
                    if let Ok(output) = transfer_document(&input) {
                        parse_document(&output).unwrap_or_else(|error| {
                            panic!("writer output for {file_name} was rejected: {error}")
                        });
                    }
                }
                _ => unreachable!(),
            }
        }
    }

    Ok(())
}
