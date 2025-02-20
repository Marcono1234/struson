//! Utility module for UTF-8 data handling

/// Maximum number of UTF-8 bytes needed to encode one Unicode `char`
pub(crate) const MAX_BYTES_PER_CHAR: usize = 4;

/// Whether the byte is a 1 byte UTF-8 encoded char; that means the byte itself represents an ASCII character
pub(crate) fn is_1byte(b: u8) -> bool {
    b <= 0x7F
}

const _2BYTE_MASK: u8 = 0b1110_0000;
/// Bit mask which matches the value bits of the 2 byte start
const _2BYTE_MASK_VAL: u8 = !_2BYTE_MASK;

/// Whether the byte is the start of a 2 byte UTF-8 encoded char
pub(crate) fn is_2byte_start(b: u8) -> bool {
    // 110x_xxxx
    (b & _2BYTE_MASK) == 0b1100_0000
}

const _3BYTE_MASK: u8 = 0b1111_0000;
/// Bit mask which matches the value bits of the 3 byte start
const _3BYTE_MASK_VAL: u8 = !_3BYTE_MASK;

/// Whether the byte is the start of a 3 byte UTF-8 encoded char
pub(crate) fn is_3byte_start(b: u8) -> bool {
    // 1110_xxxx
    (b & _3BYTE_MASK) == 0b1110_0000
}

const _4BYTE_MASK: u8 = 0b1111_1000;
/// Bit mask which matches the value bits of the 4 byte start
const _4BYTE_MASK_VAL: u8 = !_4BYTE_MASK;

/// Whether the byte is the start of a 4 byte UTF-8 encoded char
pub(crate) fn is_4byte_start(b: u8) -> bool {
    // 1111_0xxx
    (b & _4BYTE_MASK) == 0b1111_0000
}

const CONT_MASK: u8 = 0b1100_0000;
/// Bit mask which matches the value bits of the continuation byte
const CONT_MASK_VAL: u8 = !CONT_MASK;

/// Whether the byte is a continuation byte of a char which is UTF-8 encoded as 2, 3 or 4 bytes;
/// that means it is not the first byte for those multi-byte UTF-8 chars
pub(crate) fn is_continuation(b: u8) -> bool {
    // 10xx_xxxx
    (b & CONT_MASK) == 0b1000_0000
}

/// Whether the 2 bytes UTF-8 encoding is valid
pub(crate) fn is_valid_2bytes(b0: u8, b1: u8) -> bool {
    // caller should have verified this
    debug_assert!(is_2byte_start(b0) && is_continuation(b1));
    let code_point = u32::from(b0 & _2BYTE_MASK_VAL) << 6 | u32::from(b1 & CONT_MASK_VAL);
    // Verify no 'overlong encoding' of lower code points
    code_point >= 0x80
}

/// Whether the 3 bytes UTF-8 encoding is valid
pub(crate) fn is_valid_3bytes(b0: u8, b1: u8, b2: u8) -> bool {
    // caller should have verified this
    debug_assert!(is_3byte_start(b0) && is_continuation(b1) && is_continuation(b2));
    let code_point = u32::from(b0 & _3BYTE_MASK_VAL) << 12
        | u32::from(b1 & CONT_MASK_VAL) << 6
        | u32::from(b2 & CONT_MASK_VAL);
    // Verify no 'overlong encoding' of lower code points, and no UTF-16 surrogate chars encoded in UTF-8
    code_point >= 0x800 && !matches!(code_point, 0xD800..=0xDFFF)
}

/// Whether the 4 bytes UTF-8 encoding is valid
pub(crate) fn is_valid_4bytes(b0: u8, b1: u8, b2: u8, b3: u8) -> bool {
    // caller should have verified this
    debug_assert!(
        is_4byte_start(b0) && is_continuation(b1) && is_continuation(b2) && is_continuation(b3)
    );
    let code_point = u32::from(b0 & _4BYTE_MASK_VAL) << 18
        | u32::from(b1 & CONT_MASK_VAL) << 12
        | u32::from(b2 & CONT_MASK_VAL) << 6
        | u32::from(b3 & CONT_MASK_VAL);

    // Verify no 'overlong encoding' of lower code points, and no invalid code point > U+10FFFF
    matches!(code_point, 0x10000..=0x10FFFF)
}

/// For debug builds: Verifies that the bytes are valid UTF-8 data
pub(crate) fn debug_assert_valid_utf8(message: &str, bytes: &[u8]) {
    if cfg!(debug_assertions) {
        if let Err(e) = std::str::from_utf8(bytes) {
            panic!("{message}: {e:?}; bytes: {bytes:02X?}")
        }
    }
}

fn debug_assert_valid_utf8_struson(bytes: &[u8]) {
    debug_assert_valid_utf8(
        "Unexpected: Invalid UTF-8 bytes detected, report this to the Struson maintainers",
        bytes,
    );
}

/// Converts bytes to a `str`, possibly without validating that the bytes are valid UTF-8 data
///
/// Must only be called if UTF-8 validation on the bytes has already been performed manually.
pub(crate) fn to_str_unchecked(bytes: &[u8]) -> &str {
    debug_assert_valid_utf8_struson(bytes);
    // TODO: Once confident enough that UTF-8 validation in this crate is correct, use `std::str::from_utf8_unchecked` instead
    std::str::from_utf8(bytes).unwrap()
}

/// Converts bytes to a `String`, possibly without validating that the bytes are valid UTF-8 data
///
/// Must only be called if UTF-8 validation on the bytes has already been performed manually.
pub(crate) fn to_string_unchecked(bytes: Vec<u8>) -> String {
    debug_assert_valid_utf8_struson(&bytes);
    // TODO: Once confident enough that UTF-8 validation in this crate is correct, use `String::from_utf8_unchecked` instead
    String::from_utf8(bytes).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::panic::UnwindSafe;

    #[must_use] // caller must perform assertion on panic message
    fn assert_panics<R>(f: impl FnOnce() -> R + UnwindSafe) -> String {
        if let Err(panic_value) = std::panic::catch_unwind(f) {
            match panic_value.downcast::<String>() {
                Ok(message) => *message,
                Err(panic_value) => {
                    panic!("Panic value should have been a String, but is: {panic_value:?}")
                }
            }
        } else {
            panic!("Expression should have panicked");
        }
    }

    #[cfg(debug_assertions)] // validation is only performed when debug assertions are enabled
    #[test]
    fn to_str_unchecked_invalid() {
        // Overlong UTF-8 encoding for two bytes
        let message = assert_panics(|| to_str_unchecked(b"\xC1\xBF"));
        // Check prefix and suffix but ignore the error message from Rust in the middle
        assert!(
            message.starts_with("Unexpected: Invalid UTF-8 bytes detected, report this to the Struson maintainers: "),
            "Unexpected prefix for message: {message}"
        );
        assert!(
            message.ends_with("; bytes: [C1, BF]"),
            "Unexpected suffix for message: {message}"
        );
    }

    #[cfg(debug_assertions)] // validation is only performed when debug assertions are enabled
    #[test]
    fn to_string_unchecked_invalid() {
        // Overlong UTF-8 encoding for two bytes
        let message = assert_panics(|| to_string_unchecked(b"\xC1\xBF".to_vec()));
        // Check prefix and suffix but ignore the error message from Rust in the middle
        assert!(message.starts_with(
            "Unexpected: Invalid UTF-8 bytes detected, report this to the Struson maintainers: "),
            "Unexpected prefix for message: {message}"
        );
        assert!(
            message.ends_with("; bytes: [C1, BF]"),
            "Unexpected suffix for message: {message}"
        );
    }
}
