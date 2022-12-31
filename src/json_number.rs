//! Internal module for parsing / validating JSON numbers

pub fn consume_json_number<E, F: FnMut() -> Result<Option<u8>, E>, C: FnMut(u8)>(
    consume_current_peek_next: &mut F,
    consumer: &mut C,
    first_byte: u8,
) -> Result<bool, E> {
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

        consumer(byte);

        // In the first iteration this consumes the `first_byte` argument
        let peeked_byte = consume_current_peek_next()?;
        if peeked_byte.is_none() {
            has_trailing_number_chars = false;
            break;
        } else {
            byte = peeked_byte.unwrap();
        }
    }

    if has_trailing_number_chars
        || !(state == State::IntZero
            || state == State::IntNonZero
            || state == State::DecimalDigit
            || state == State::ExpDigit)
    {
        Ok(false)
    } else {
        Ok(true)
    }
}
