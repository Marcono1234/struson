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
    #[derive(PartialEq)]
    enum State {
        Start,
        Minus,
        IntZero,
        IntNonZero,
        DecimalPoint,
        DecimalDigit,
        ExpE,
        ExpSign,
        ExpDigit,
    }

    let mut byte = first_byte;
    let mut state = State::Start;
    // Used to track unexpected trailing number chars, to detect the whole number
    // as invalid, e.g. "01"
    let mut has_trailing_number_chars = true;
    let mut exponent_digits_count = 0;

    loop {
        // TODO: Rewrite this to first check state, then byte, to make it easier to read?

        if byte == b'-' {
            if state == State::Start {
                state = State::Minus;
            } else if state == State::ExpE {
                state = State::ExpSign;
            } else {
                break;
            }
        } else if byte == b'0' {
            if state == State::Start || state == State::Minus {
                state = State::IntZero;
            } else if state == State::IntNonZero {
                state = State::IntNonZero;
            } else if state == State::DecimalPoint || state == State::DecimalDigit {
                state = State::DecimalDigit;
            } else if state == State::ExpE || state == State::ExpSign || state == State::ExpDigit {
                state = State::ExpDigit;

                // Don't increment for leading 0s
                if exponent_digits_count > 0 {
                    exponent_digits_count += 1;
                }
            } else {
                break;
            }
        } else if (b'1'..=b'9').contains(&byte) {
            if state == State::Start || state == State::Minus || state == State::IntNonZero {
                state = State::IntNonZero;
            } else if state == State::DecimalPoint || state == State::DecimalDigit {
                state = State::DecimalDigit;
            } else if state == State::ExpE || state == State::ExpSign || state == State::ExpDigit {
                state = State::ExpDigit;
                exponent_digits_count += 1;
            } else {
                break;
            }
        } else if byte == b'.' {
            if state == State::IntZero || state == State::IntNonZero {
                state = State::DecimalPoint;
            } else {
                break;
            }
        } else if byte == b'e' || byte == b'E' {
            if state == State::IntZero || state == State::IntNonZero || state == State::DecimalDigit
            {
                state = State::ExpE;
            } else {
                break;
            }
        } else if byte == b'+' {
            if state == State::ExpE {
                state = State::ExpSign;
            } else {
                break;
            }
        } else {
            has_trailing_number_chars = false;
            break;
        }

        // In the first iteration this consumes the `first_byte` argument
        if let Some(peeked_byte) = reader.consume_current_peek_next()? {
            byte = peeked_byte;
        } else {
            has_trailing_number_chars = false;
            break;
        }
    }

    if has_trailing_number_chars
        || !(state == State::IntZero
            || state == State::IntNonZero
            || state == State::DecimalDigit
            || state == State::ExpDigit)
    {
        Ok(None)
    } else {
        Ok(Some(exponent_digits_count))
    }
}
