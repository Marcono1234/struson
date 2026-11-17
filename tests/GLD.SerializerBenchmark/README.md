# GLD.SerializerBenchmark RFC 8259 test data

The cases in rfc8259.json are reduced from
https://github.com/leo-gan/GLD.SerializerBenchmark/blob/4930841a529441107e1c89cc1ac90c982db0069a/compliance/data/json/rfc8259.json
in https://github.com/leo-gan/GLD.SerializerBenchmark.

- Upstream commit: 4930841a529441107e1c89cc1ac90c982db0069a
- SHA-256 of the unmodified upstream file: c7ff5fee6b98202d032b35ee621fea75306dba8a8542b2115bf7793b0157ad19
- License: MIT; see LICENSE.

The reduced file keeps the upstream document metadata and, for each case, only
id, input, input_encoding, expect, and decoded when present. It is pretty-printed
JSON.

## Regeneration

Check out GLD.SerializerBenchmark at the pinned commit and set
GLD_RFC8259_SOURCE to the local path of its compliance/data/json/rfc8259.json.
In tests/json_test_suite.rs, temporarily uncomment the #[test] line directly
above shrink_test_file and remove the #[expect(unused)] line directly above it,
then run this from the Struson repository root:

~~~sh
GLD_RFC8259_SOURCE=/path/to/GLD.SerializerBenchmark/compliance/data/json/rfc8259.json \
  cargo test --test json_test_suite shrink_test_file
~~~

Restore both lines afterwards. The helper reads a local file instead of
downloading it so regeneration is offline and uses the explicitly pinned
source revision.
