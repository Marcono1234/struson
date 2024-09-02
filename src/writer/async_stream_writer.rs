#![allow(missing_docs)]
//! Async streaming implementation of [`JsonWriter`]
use crate::utf8;
use std::{
    io::{ErrorKind, Write},
    pin::Pin,
    str::Utf8Error,
};
use tokio::io::{AsyncWrite, AsyncWriteExt};

use super::*;

/// A JSON writer implementation which writes data to a [`Write`]
///
/// This writer internally buffers data so it is normally not necessary to wrap the provided
/// writer in a [`std::io::BufWriter`].
///
/// The data written to the underlying writer will be valid UTF-8 data if the JSON document
/// is finished properly by calling [`JsonWriter::finish_document`]. No leading byte order mark (BOM)
/// is written.
///
/// If the underlying writer returns an error of kind [`ErrorKind::Interrupted`], this
/// JSON writer will keep retrying to write the data.
pub struct AsyncJsonStreamWriter<W> {
    // When adding more fields to this struct, adjust the Debug implementation below, if necessary
    writer: W,
    buf: [u8; WRITER_BUF_SIZE],
    /// Index (starting at 0) within [`buf`](Self::buf) where to write next,
    /// respectively how many bytes have already been written to the buffer
    buf_write_pos: usize,
    /// Whether the current array or object is empty, or at top-level whether
    /// at least one value has been written already
    is_empty: bool,
    expects_member_name: bool,
    stack: Vec<StackValue>,
    is_string_value_writer_active: bool,
    indentation_level: u32,

    writer_settings: WriterSettings,
}

// Implementation with public constructor methods
impl<W: AsyncWrite + Unpin> AsyncJsonStreamWriter<W> {
    /// Creates a JSON writer with [default settings](WriterSettings::default)
    pub fn new(writer: W) -> Self {
        AsyncJsonStreamWriter::new_custom(writer, WriterSettings::default())
    }

    /// Creates a JSON writer with custom settings
    ///
    /// The settings can be used to customize how the JSON output will look like.
    pub fn new_custom(writer: W, writer_settings: WriterSettings) -> Self {
        Self {
            writer,
            buf: [0_u8; WRITER_BUF_SIZE],
            buf_write_pos: 0,
            is_empty: true,
            expects_member_name: false,
            stack: Vec::with_capacity(16),
            is_string_value_writer_active: false,
            indentation_level: 0,
            writer_settings,
        }
    }

    /// Unwrap the inner writer.
    pub fn into_inner(self) -> W {
        self.writer
    }
}

// Implementation with low level byte writing methods
impl<W: AsyncWrite + Unpin> AsyncJsonStreamWriter<W> {
    async fn write_bytes(&mut self, bytes: &[u8]) -> Result<(), IoError> {
        let mut pos = 0;
        while pos < bytes.len() {
            let copied_count = (self.buf.len() - self.buf_write_pos).min(bytes.len() - pos);
            self.buf[self.buf_write_pos..(self.buf_write_pos + copied_count)]
                .copy_from_slice(&bytes[pos..(pos + copied_count)]);
            self.buf_write_pos += copied_count;
            pos += copied_count;

            if self.buf_write_pos >= self.buf.len() {
                // write_all retries on `ErrorKind::Interrupted`, as desired
                Pin::new(&mut self.writer).write_all(&self.buf).await?;
                self.buf_write_pos = 0;
            }
        }

        Ok(())
    }

    async fn flush(&mut self) -> Result<(), IoError> {
        // write_all retries on `ErrorKind::Interrupted`, as desired
        self.writer
            .write_all(&self.buf[0..self.buf_write_pos])
            .await?;
        self.buf_write_pos = 0;
        self.writer.flush().await
    }
}

// Implementation with JSON structure state inspection methods, and general value methods
impl<W: AsyncWrite + Unpin> AsyncJsonStreamWriter<W> {
    fn is_in_array(&self) -> bool {
        self.stack.last().map_or(false, |v| v == &StackValue::Array)
    }

    fn is_in_object(&self) -> bool {
        self.stack
            .last()
            .map_or(false, |v| v == &StackValue::Object)
    }

    fn increase_indentation(&mut self) {
        self.indentation_level += 1;
    }

    fn decrease_indentation(&mut self) {
        self.indentation_level -= 1;
    }

    async fn write_indentation(&mut self) -> Result<(), IoError> {
        for _ in 0..self.indentation_level {
            self.write_bytes(b"  ").await?;
        }
        Ok(())
    }

    async fn before_container_element(&mut self) -> Result<(), IoError> {
        if self.is_empty {
            if self.writer_settings.pretty_print {
                // Convert "[" (respectively "{") to "[\n..."
                self.write_bytes(b"\n").await?;
                self.increase_indentation();
                self.write_indentation().await?;
            }
        } else {
            #[allow(clippy::collapsible_else_if)]
            if self.writer_settings.pretty_print {
                self.write_bytes(b",\n").await?;
                self.write_indentation().await?;
            } else {
                self.write_bytes(b",").await?;
            }
        }
        Ok(())
    }

    async fn before_value(&mut self) -> Result<(), IoError> {
        if self.is_string_value_writer_active {
            panic!("Incorrect writer usage: Cannot finish document when string value writer is still active");
        }
        if self.expects_member_name {
            panic!("Incorrect writer usage: Cannot write value when name is expected");
        }

        let is_behind_top_level = !self.is_empty && self.stack.is_empty();
        if is_behind_top_level {
            match &self.writer_settings.multi_top_level_value_separator {
                None => panic!("Incorrect writer usage: Cannot write multiple top-level values when not enabled in writer settings"),
                Some(separator) => {
                    // TODO: Avoid clone() here; compiler currently does not allow borrowing it because
                    //   `write_bytes` has a mutable borrow to self
                    let separator = separator.clone();
                    self.write_bytes(separator.as_bytes()).await?;
                },
            }
        } else if self.is_in_array() {
            self.before_container_element().await?;
        }
        self.is_empty = false;

        if self.is_in_object() {
            // After this value a name will be expected
            self.expects_member_name = true;
        }

        Ok(())
    }

    async fn on_container_end(&mut self) -> Result<(), IoError> {
        self.stack.pop();

        if !self.is_empty && self.writer_settings.pretty_print {
            self.write_bytes(b"\n").await?;
            self.decrease_indentation();
            self.write_indentation().await?;
        }

        // Enclosing container is not empty since this method call here is processing its child
        self.is_empty = false;

        // If after pop() call above currently in object, then expecting a member name
        self.expects_member_name = self.is_in_object();
        Ok(())
    }
}

// Implementation with string writing methods
impl<W: AsyncWrite + Unpin> AsyncJsonStreamWriter<W> {
    fn should_escape(&self, c: char) -> bool {
        matches!(c, '"' | '\\')
        // Control characters which must be escaped per JSON specification
        || matches!(c, '\u{0}'..='\u{1F}')
            || (self.writer_settings.escape_all_non_ascii && !c.is_ascii())
            || (self.writer_settings.escape_all_control_chars && c.is_control())
    }

    async fn write_escaped_char(&mut self, c: char) -> Result<(), IoError> {
        fn get_unicode_escape(value: u32) -> [u8; 4] {
            // For convenience `value` is u32, but it is actually u16
            debug_assert!(value <= u16::MAX as u32);

            fn to_hex(i: u32) -> u8 {
                match i {
                    0..=9 => b'0' + i as u8,
                    10..=15 => b'A' + (i - 10) as u8,
                    _ => unreachable!("Unexpected value {i}"),
                }
            }

            [
                to_hex(value >> 12 & 15),
                to_hex(value >> 8 & 15),
                to_hex(value >> 4 & 15),
                to_hex(value & 15),
            ]
        }

        let escape = match c {
            '"' => "\\\"",
            '\\' => "\\\\",
            '/' => "\\/",
            '\u{0008}' => "\\b",
            '\u{000C}' => "\\f",
            '\n' => "\\n",
            '\r' => "\\r",
            '\t' => "\\t",
            '\0'..='\u{FFFF}' => {
                self.write_bytes(b"\\u").await?;
                self.write_bytes(&get_unicode_escape(c as u32)).await?;
                return Ok(());
            }
            _ => {
                // Encode as surrogate pair
                let temp = (c as u32) - 0x10000;
                let high = (temp >> 10) + 0xD800;
                let low = (temp & ((1 << 10) - 1)) + 0xDC00;

                self.write_bytes(b"\\u").await?;
                self.write_bytes(&get_unicode_escape(high)).await?;

                self.write_bytes(b"\\u").await?;
                self.write_bytes(&get_unicode_escape(low)).await?;
                return Ok(());
            }
        };
        self.write_bytes(escape.as_bytes()).await
    }

    async fn write_string_value_piece(&mut self, value: &str) -> Result<(), IoError> {
        let bytes = value.as_bytes();
        let mut next_to_write_index = 0;

        for (index, char) in value.char_indices() {
            if self.should_escape(char) {
                if index > next_to_write_index {
                    self.write_bytes(&bytes[next_to_write_index..index]).await?;
                }
                self.write_escaped_char(char).await?;
                next_to_write_index = index + char.len_utf8();
            }
        }
        // Write remaining bytes
        if next_to_write_index < bytes.len() {
            self.write_bytes(&bytes[next_to_write_index..]).await?;
        }

        Ok(())
    }

    async fn write_string_value(&mut self, value: &str) -> Result<(), IoError> {
        self.write_bytes(b"\"").await?;
        self.write_string_value_piece(value).await?;
        self.write_bytes(b"\"").await
    }

    async fn number_value_str(&mut self, number_str: &str) -> Result<(), IoError> {
        self.before_value().await?;
        self.write_bytes(number_str.as_bytes()).await
    }

    async fn fp_number_value_str(&mut self, number_str: &str) -> Result<(), JsonNumberError> {
        self.before_value().await?;
        self.write_bytes(number_str.as_bytes())
            .await
            .map_err(JsonNumberError::IoError)
    }
}

impl<W: AsyncWrite + Unpin + Send> AsyncJsonStreamWriter<W> {
    pub async fn begin_object(&mut self) -> Result<(), IoError> {
        self.before_value().await?;
        self.stack.push(StackValue::Object);
        self.is_empty = true;
        self.expects_member_name = true;
        self.write_bytes(b"{").await
    }

    pub async fn name(&mut self, name: &str) -> Result<(), IoError> {
        if !self.expects_member_name {
            panic!("Incorrect writer usage: Cannot write name when name is not expected");
        }
        if self.is_string_value_writer_active {
            panic!("Incorrect writer usage: Cannot finish document when string value writer is still active");
        }
        self.before_container_element().await?;
        self.write_string_value(name).await?;
        self.write_bytes(if self.writer_settings.pretty_print {
            b": "
        } else {
            b":"
        })
        .await?;
        self.expects_member_name = false;

        Ok(())
    }

    pub async fn end_object(&mut self) -> Result<(), IoError> {
        if !self.is_in_object() {
            panic!("Incorrect writer usage: Cannot end object when not inside object");
        }
        if self.is_string_value_writer_active {
            panic!("Incorrect writer usage: Cannot end object when string value writer is still active");
        }
        if !self.expects_member_name {
            panic!("Incorrect writer usage: Cannot end object when member value is expected");
        }
        self.on_container_end().await?;
        self.write_bytes(b"}").await
    }

    pub async fn begin_array(&mut self) -> Result<(), IoError> {
        self.before_value().await?;
        self.stack.push(StackValue::Array);
        self.is_empty = true;

        // Clear this because it is only relevant for objects; will be restored when entering parent object (if any) again
        self.expects_member_name = false;

        self.write_bytes(b"[").await
    }

    pub async fn end_array(&mut self) -> Result<(), IoError> {
        if !self.is_in_array() {
            panic!("Incorrect writer usage: Cannot end array when not inside array");
        }
        if self.is_string_value_writer_active {
            panic!(
                "Incorrect writer usage: Cannot end array when string value writer is still active"
            );
        }
        self.on_container_end().await?;
        self.write_bytes(b"]").await
    }

    pub async fn bool_value(&mut self, value: bool) -> Result<(), IoError> {
        self.before_value().await?;
        self.write_bytes(if value { b"true" } else { b"false" })
            .await
    }

    pub async fn string_value(&mut self, value: &str) -> Result<(), IoError> {
        self.before_value().await?;
        self.write_string_value(value).await
    }

    pub async fn null_value(&mut self) -> Result<(), IoError> {
        self.before_value().await?;
        self.write_bytes(b"null").await
    }

    pub async fn number_value<N: FiniteNumber + Send>(&mut self, value: N) -> Result<(), IoError> {
        self.number_value_str(&value.get_json_number()?).await
    }

    pub async fn fp_number_value<N: FloatingPointNumber + Send>(
        &mut self,
        value: N,
    ) -> Result<(), JsonNumberError> {
        self.fp_number_value_str(&value.get_json_number()?).await
    }

    pub async fn number_value_from_string(&mut self, value: &str) -> Result<(), JsonNumberError> {
        if is_valid_json_number(value) {
            self.before_value().await?;
            self.write_bytes(value.as_bytes()).await?;
            Ok(())
        } else {
            Err(JsonNumberError::InvalidNumber(format!(
                "invalid JSON number: {value}"
            )))
        }
    }

    pub async fn finish_document(mut self) -> Result<(), IoError> {
        if self.is_string_value_writer_active {
            panic!("Incorrect writer usage: Cannot finish document when string value writer is still active");
        }
        if self.expects_member_name {
            panic!("Incorrect writer usage: Cannot finish document when member name is expected");
        }
        if self.stack.is_empty() {
            if self.is_empty {
                panic!("Incorrect writer usage: Cannot finish document when no value has been written yet");
            }
        } else {
            panic!("Incorrect writer usage: Cannot finish document when top-level value is not finished");
        }
        self.flush().await
    }

    pub async fn start_string_value_writer(&mut self) -> Result<(), IoError> {
        self.before_value().await?;
        self.write_bytes(b"\"").await?;
        self.is_string_value_writer_active = true;
        Ok(())
    }

    pub async fn write_string_value_writer(&mut self, buf: &[u8]) -> std::io::Result<()> {
        if !self.is_string_value_writer_active {
            panic!("string value writer not active, wrong API usage");
        };
        if buf.is_empty() {
            return Ok(());
        }
        self.write_bytes(buf).await?;
        Ok(())
    }

    pub async fn finish_string_value_writer(&mut self) -> Result<(), IoError> {
        if !self.is_string_value_writer_active {
            panic!("string value writer not active, wrong API usage");
        };
        self.write_bytes(b"\"").await?;
        self.is_string_value_writer_active = false;
        Ok(())
    }
}

// TODO: Is there a way to have `W` only optionally implement `Debug`?
impl<W: Write + Debug> Debug for AsyncJsonStreamWriter<W> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug_struct = f.debug_struct("JsonStreamWriter");
        debug_struct
            .field("writer", &self.writer)
            .field("buf_count", &self.buf_write_pos);

        fn limit_str_middle(s: &str) -> String {
            let chars_count = s.chars().count();

            let prefix_len = 25;
            let suffix_len = prefix_len;

            let max_len = 55;
            // Assert that `max_len` is large enough for splitting to be possible and worth it
            assert!(max_len > prefix_len + suffix_len);

            if chars_count <= max_len {
                return s.to_owned();
            }

            let prefix_end = s.char_indices().nth(prefix_len).unwrap().0;
            let prefix = &s[..prefix_end];

            // `suffix_len - 1` because `nth_back(0)` already returns inclusive index of first char
            let suffix_start = s.char_indices().nth_back(suffix_len - 1).unwrap().0;
            let suffix = &s[suffix_start..];

            format!("{prefix} ... {suffix}")
        }

        match std::str::from_utf8(&self.buf[..self.buf_write_pos]) {
            Ok(buf_string) => {
                debug_struct.field("buf_str", &limit_str_middle(buf_string));
            }
            // In case of error buffer was likely already flushed before and split valid UTF-8;
            // loop until start of next valid substring is found
            Err(_) => {
                let mut substring_start = self.buf_write_pos;
                let mut buf_string_suffix = None;

                for i in 1..self.buf_write_pos {
                    if let Ok(suffix) = std::str::from_utf8(&self.buf[i..self.buf_write_pos]) {
                        buf_string_suffix = Some(format!("...{}", &limit_str_middle(suffix)));
                        substring_start = i;
                        break;
                    }
                }

                // Only include the bytes which could not be decoded to string
                debug_struct.field("buf...", &&self.buf[..substring_start]);

                // If no valid suffix could be decoded use "..."
                debug_struct.field(
                    "buf_str",
                    &buf_string_suffix.unwrap_or_else(|| "...".to_owned()),
                );
            }
        }

        debug_struct
            .field("is_empty", &self.is_empty)
            .field("expects_member_name", &self.expects_member_name)
            .field("stack", &self.stack)
            .field(
                "is_string_value_writer_active",
                &self.is_string_value_writer_active,
            )
            .field("indentation_level", &self.indentation_level)
            .field("writer_settings", &self.writer_settings)
            .finish()
    }
}
