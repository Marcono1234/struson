//! Internal module for parsing / validating JSON numbers

pub(crate) trait NumberBytesProvider<E> {
    /// Consumes the byte which is currently processed, and peeks at the next.
    ///
    /// Returns `None` if the end of the input has been reached.
    fn consume_current_peek_next(&mut self) -> Result<Option<u8>, E>;
}

/// Returns `None` if the number is invalid and `Some(exponent_digits_count)` if
/// the number is valid. The `exponent_digits_count` is the number of exponent
/// digits, without sign and without leading 0s.
pub(crate) fn consume_json_number<E, R: NumberBytesProvider<E>>(
    reader: &mut R,
    first_byte: u8,
) -> Result<Option<u32>, E> {
    let mut byte = first_byte;

    if byte == b'-' {
        if let Some(b) = reader.consume_current_peek_next()? {
            byte = b;
        } else {
            // Invalid number (missing integer part)
            return Ok(None);
        }
    }

    // Consume integer part, but treat 0 specially, because leading 0 before integer part is disallowed
    if (b'1'..=b'9').contains(&byte) {
        loop {
            if let Some(b) = reader.consume_current_peek_next()? {
                byte = b;
            } else {
                // Valid number with 0 exponent digits
                return Ok(Some(0));
            }

            if !byte.is_ascii_digit() {
                break;
            }
        }
    } else if byte == b'0' {
        if let Some(b) = reader.consume_current_peek_next()? {
            byte = b;
        } else {
            // Valid number with 0 exponent digits
            return Ok(Some(0));
        }
    } else {
        // Invalid number (invalid integer part)
        return Ok(None);
    }

    // Fraction part
    if byte == b'.' {
        if let Some(b) = reader.consume_current_peek_next()? {
            byte = b;
        } else {
            // Invalid number (missing decimal part)
            return Ok(None);
        }

        if !byte.is_ascii_digit() {
            // Invalid number (invalid decimal part)
            return Ok(None);
        }

        loop {
            if let Some(b) = reader.consume_current_peek_next()? {
                byte = b;
            } else {
                // Valid number with 0 exponent digits
                return Ok(Some(0));
            }

            if !byte.is_ascii_digit() {
                break;
            }
        }
    }

    // Exponent part
    let mut exponent_digits_count = 0;
    if byte == b'e' || byte == b'E' {
        if let Some(b) = reader.consume_current_peek_next()? {
            byte = b;
        } else {
            // Invalid number (missing exponent number)
            return Ok(None);
        }

        if byte == b'-' || byte == b'+' {
            if let Some(b) = reader.consume_current_peek_next()? {
                byte = b;
            } else {
                // Invalid number (missing exponent number)
                return Ok(None);
            }
        }

        // Check for '1'..='9' to ignore leading 0s for exponent digits count
        if (b'1'..=b'9').contains(&byte) {
            exponent_digits_count += 1;
        } else if byte != b'0' {
            // Invalid number (invalid exponent number)
            return Ok(None);
        }

        loop {
            if let Some(b) = reader.consume_current_peek_next()? {
                byte = b;
            } else {
                // Valid number
                return Ok(Some(exponent_digits_count));
            }

            if byte.is_ascii_digit() {
                // Ignore leading 0s for exponent digits count
                if byte != b'0' || exponent_digits_count > 0 {
                    exponent_digits_count += 1;
                }
            } else {
                break;
            }
        }
    }

    if byte.is_ascii_digit()
        || byte == b'-'
        || byte == b'+'
        || byte == b'.'
        || byte == b'e'
        || byte == b'E'
    {
        // If character after number (which is not part of number) is a number char, treat it as invalid
        // For example `01`, `1.2.3` or `1-`
        Ok(None)
    } else {
        // Valid number
        Ok(Some(exponent_digits_count))
    }
}
