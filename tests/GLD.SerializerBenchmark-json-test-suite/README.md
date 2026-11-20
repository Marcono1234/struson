# GLD.SerializerBenchmark RFC 8259 test suite

Test suite for JSON [RFC 8259](https://www.rfc-editor.org/info/rfc8259/) compliance, based on the data from <https://github.com/leo-gan/GLD.SerializerBenchmark>, see [`LICENSE`](./LICENSE).

The test suite file [`rfc8259.json`](./rfc8259.json) is derived from:\
<https://github.com/leo-gan/GLD.SerializerBenchmark/blob/4930841a529441107e1c89cc1ac90c982db0069a/compliance/data/json/rfc8259.json>

## Updating test suite file

Follow these steps to update the `rfc8259.json` file with upstream changes:

1. Download the latest `rfc8259.json` from <https://github.com/leo-gan/GLD.SerializerBenchmark>
2. Save it as `rfc8259-upstream.json` next to the existing `rfc8259.json` in this directory
3. Update the Git commit reference to the GLD.SerializerBenchmark file in this README
4. In [`tests/json_test_suite.rs`](/tests/json_test_suite.rs) uncomment the `#[test]` line for the `shrink_test_file` function, then run it as 'test' (either from IDE or with `cargo test --test json_test_suite shrink_test_file`)
5. Check the updated `rfc8259.json`, make sure it was not corrupted
6. Run the test suite
    - If necessary update the `ANY_CASE_DECISIONS` in `json_test_suite.rs`
7. Perform clean-up
    - Delete the temporary `rfc8259-upstream.json` file again
    - Comment out the `#[test]` line in `json_test_suite.rs` again
8. Commit the changes
