use thiserror::Error;

use crate::token::{FixedTokenKind, TokenKind};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Error)]
#[error("mismatched quotes")]
pub(crate) struct MismatchedQuotes;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Error)]
#[error("unterminated block comment")]
pub(crate) struct UnterminatedBlockComment;

/// Lexes a doc comment, returning the token kind and the length of the token.
///
/// # Examples
///
/// ```
/// assert_eq!(lex_doc_comment("/// hello"), Some((TokenKind::DocComment, 9)));
/// assert_eq!(lex_doc_comment("/// hello\nnew line"), Some((TokenKind::DocComment, 9)));
/// assert_eq!(lex_doc_comment("// not a doc comment"), None);
/// ```
pub(crate) fn lex_doc_comment(rest: &str) -> Option<(TokenKind, usize)> {
    Some((
        TokenKind::DocComment,
        find_line_break(rest.strip_prefix("///")?) + 3,
    ))
}

/// Lexes an integer or float, returning the token kind and the length of the token.
///
/// # Examples
///
/// ```
/// # use crate::token::TokenKind;
/// assert_eq!(lex_integer_or_float("123      "), Some((TokenKind::Integer, 3)));
/// assert_eq!(lex_integer_or_float("0xFF     "), Some((TokenKind::Integer, 4)));
/// assert_eq!(lex_integer_or_float("0b101010 "), Some((TokenKind::Integer, 8)));
/// assert_eq!(lex_integer_or_float("0o777    "), Some((TokenKind::Integer, 5)));
///
/// assert_eq!(lex_integer_or_float("42.0  "), Some((TokenKind::Float, 4)));
/// assert_eq!(lex_integer_or_float("42E3  "), Some((TokenKind::Float, 4)));
/// assert_eq!(lex_integer_or_float("10E+3 "), Some((TokenKind::Float, 5)));
/// assert_eq!(lex_integer_or_float("10E-3 "), Some((TokenKind::Float, 5)));
/// ```
pub(crate) fn lex_integer_or_float(rest: &str) -> Option<(TokenKind, usize)> {
    let after_initial_digit = rest.strip_prefix(|c: char| c.is_ascii_digit())?;
    Some(
        if let Some(after_base) = after_initial_digit.strip_prefix(['B', 'b', 'O', 'o', 'X', 'x']) {
            let end =
                after_base.trim_start_matches(|c: char| c.is_ascii_alphanumeric() || c == '_');
            (TokenKind::Integer, rest.len() - end.len())
        } else {
            let mut token_kind = TokenKind::Integer;
            let mut after_digits =
                after_initial_digit.trim_start_matches(|c: char| c.is_ascii_digit() || c == '_');

            if let Some(after_period) = after_digits.strip_prefix('.') {
                token_kind = TokenKind::Float;
                after_digits =
                    after_period.trim_start_matches(|c: char| c.is_ascii_digit() || c == '_');
            }

            if let Some(after_exponent) = after_digits.strip_prefix(['E', 'e']) {
                token_kind = TokenKind::Float;
                after_digits = after_exponent
                    .strip_prefix(['+', '-'])
                    .unwrap_or(after_exponent)
                    .trim_start_matches(|c: char| c.is_ascii_digit() || c == '_');
            }

            let end =
                after_digits.trim_start_matches(|c: char| c.is_ascii_alphanumeric() || c == '_');

            (token_kind, rest.len() - end.len())
        },
    )
}

/// Lexes a char or label, returning the token kind and the length of the token.
///
/// Implementing label detection can be kindof hard to wrap your head around.
///
/// Examples for valid chars and labels:
///
/// ```txt
/// input | ident | ' after
///       | chars | ident
/// ------+-------+--------
/// ''    |     0 | true
/// 'a'   |     1 | true
/// 'ab'  |     2 | true
/// '?'   |     0 | false
/// ------+-------+--------
/// 'a    |     1 | false
/// 'ab   |     2 | false
/// ```
///
/// Truth table based on the examples above:
///
/// ```txt
///   | true | false
/// --+------+------
/// 0 | char | char
/// 1 | char | label
/// 2 | char | label
/// ```
///
/// Reading from the truth table: `is_char = (ident chars) < 1 || (' after ident)`
///
/// # Examples
///
/// ```
/// # use crate::token::TokenKind;
/// assert_eq!(lex_char_or_label("'    "), None);
/// assert_eq!(lex_char_or_label("'?   "), Some((TokenKind::Label, 2)));
/// assert_eq!(lex_char_or_label("'?'  "), Some((TokenKind::Label, 2)));
/// assert_eq!(lex_char_or_label("''   "), Some((TokenKind::Char, 0)));
/// assert_eq!(lex_char_or_label("'a   "), None);
/// assert_eq!(lex_char_or_label("'a'  "), Some((TokenKind::Char, 3)));
/// assert_eq!(lex_char_or_label("'ab  "), None);
/// assert_eq!(lex_char_or_label("'ab' "), Some((TokenKind::Char, 4)));
/// ```
pub(crate) fn lex_char_or_label(
    rest: &str,
) -> Result<Option<(TokenKind, usize)>, MismatchedQuotes> {
    let Some(after_quote) = rest.strip_prefix('\'') else {
        return Ok(None);
    };
    let after_ident_chars =
        after_quote.trim_start_matches(|c: char| c.is_ascii_alphanumeric() || c == '_');
    let ident_chars = after_quote.len() - after_ident_chars.len();
    let quote_after_ident = after_ident_chars.starts_with('\'');
    Ok(if ident_chars < 1 || quote_after_ident {
        Some((
            TokenKind::Char,
            rest.len() - lex_quoted_content(after_ident_chars, '\'')?.len(),
        ))
    } else {
        Some((TokenKind::Label, rest.len() - after_ident_chars.len()))
    })
}

/// Lexes a quoted string or byte-string/char, returning the token kind and the length of the token.
///
/// Regular chars are handled by [`lex_char_or_label`], since distingushing those is a bit tricky.
pub(crate) fn lex_quoted(rest: &str) -> Result<Option<(TokenKind, usize)>, MismatchedQuotes> {
    let (after_quote, end_quote) = if let Some(after_quote) = rest.strip_prefix("b'") {
        (after_quote, '\'')
    } else if let Some(after_quote) = rest.strip_prefix('"').or_else(|| rest.strip_prefix("b\"")) {
        (after_quote, '"')
    } else {
        return Ok(None);
    };

    let end = lex_quoted_content(after_quote, end_quote)?;
    Ok(Some((TokenKind::String, rest.len() - end.len())))
}

/// Lexes a raw string or byte-string, returning the token kind and the length of the token.
pub(crate) fn lex_raw_string(rest: &str) -> Result<Option<(TokenKind, usize)>, MismatchedQuotes> {
    let after_r = if rest.starts_with("r#") || rest.starts_with("r\"") {
        &rest[1..]
    } else if rest.starts_with("br#") || rest.starts_with("br\"") {
        &rest[2..]
    } else {
        return Ok(None);
    };

    let after_pound = after_r.trim_matches('#');
    let start_pounds = &after_r[0..(after_r.len() - after_pound.len())];
    let mut after_quote = after_pound.strip_prefix('"').unwrap_or(after_pound);
    loop {
        after_quote = after_quote.trim_start_matches(|c: char| c != '"');
        if let Some(end_pounds) = after_quote.strip_prefix('"') {
            if let Some(end) = end_pounds.strip_prefix(start_pounds) {
                break Ok(Some((TokenKind::String, rest.len() - end.len())));
            }
            after_quote = end_pounds;
        } else {
            return Err(MismatchedQuotes);
        }
    }
}

/// Lexes a keyword or ident, returning the token kind and the length of the token.
pub(crate) fn lex_keyword_or_ident(rest: &str) -> Option<(TokenKind, usize)> {
    if !rest.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') {
        return None;
    }

    let ident_len = rest
        .find(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .unwrap_or(rest.len());
    Some(
        if let Some(keyword) = FixedTokenKind::parse_keyword(rest[..ident_len].as_bytes()) {
            (keyword.into(), ident_len)
        } else {
            (TokenKind::Ident, ident_len)
        },
    )
}

/// Advances `pos` over whitespace characters and returns `true` if the end of input was reached.
///
/// Whitespace also includes comments (except for doc-comments).
pub(crate) fn lex_whitespace(
    code: &str,
    pos: &mut usize,
) -> Result<bool, UnterminatedBlockComment> {
    loop {
        match code[*pos..].bytes().next() {
            None => break Ok(true),
            Some(c) if c.is_ascii_whitespace() => {
                *pos = code[*pos + 1..]
                    .find(|c: char| !c.is_ascii_whitespace())
                    .map_or(code.len(), |len| *pos + len + 1);
            }
            Some(b'/') => {
                if code[*pos + 1..].starts_with("//") {
                    break Ok(false);
                } else if code[*pos + 1..].starts_with('/') {
                    *pos += 2 + find_line_break(&code[*pos + 2..]);
                } else if code[*pos + 1..].starts_with('*') {
                    let start_len = code[*pos..].len();
                    let mut after_block_comment = &code[*pos + 2..];
                    let mut nesting: usize = 0;
                    loop {
                        let Some(len) = after_block_comment.find("*/") else {
                            return Err(UnterminatedBlockComment);
                        };
                        if let Some(open) = after_block_comment[..len].find("/*") {
                            after_block_comment = &after_block_comment[open + 2..];
                            nesting += 1;
                        } else {
                            after_block_comment = &after_block_comment[len + 2..];
                            if nesting == 0 {
                                *pos += start_len - after_block_comment.len();
                                break;
                            }
                            nesting -= 1;
                        }
                    }
                } else {
                    break Ok(false);
                }
            }
            _ => break Ok(false),
        }
    }
}

/// Lexes the contents of something quoted, returning the rest of the string.
fn lex_quoted_content(mut after_quote: &str, end_quote: char) -> Result<&str, MismatchedQuotes> {
    loop {
        let quote_or_backslash =
            after_quote.trim_start_matches(|c: char| c != end_quote && c != '\\');
        if quote_or_backslash.is_empty() {
            return Err(MismatchedQuotes);
        }
        if let Some(end) = quote_or_backslash.strip_prefix(end_quote) {
            break Ok(end);
        }
        let Some(after_escape) = quote_or_backslash.get(2..) else {
            return Err(MismatchedQuotes);
        };
        after_quote = after_escape;
    }
}

/// Returns the position after the next line break in `code`.
fn find_line_break(code: &str) -> usize {
    let Some(line_break) = code
        .bytes()
        .enumerate()
        .find_map(|(pos, byte)| [b'\n', b'\r'].contains(&byte).then_some(pos))
    else {
        return code.len();
    };

    if let Some(b'\n') = code.as_bytes().get(line_break + 1) {
        line_break + 2
    } else {
        line_break + 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lex_integer_or_float() {
        todo!()
    }

    #[test]
    fn test_lex_char_or_label() {
        todo!()
    }

    #[test]
    fn test_lex_quoted() {
        todo!()
    }

    #[test]
    fn test_lex_raw_string() {
        todo!()
    }

    #[test]
    fn test_lex_keyword_or_ident() {
        todo!()
    }

    #[test]
    fn test_lex_whitespace() {
        fn test(code: &str, expected_pos: usize, result: Result<bool, UnterminatedBlockComment>) {
            let mut pos = 0;
            assert_eq!(lex_whitespace(code, &mut pos), result);
            assert_eq!(pos, expected_pos);
        }

        test("", 0, Ok(true));
        test("foo", 0, Ok(false));
        test(" \n\t", 3, Ok(true));
        test(" \n\tfoo", 3, Ok(false));
        test("// foo", 6, Ok(true));
        test("// foo\n", 7, Ok(true));
        test("// foo\nbar", 7, Ok(false));
        test("/// foo", 0, Ok(false));
        test("/*foo bar*/", 11, Ok(true));
        test("/*foo bar*/bar", 11, Ok(false));
        test("/*/", 0, Err(UnterminatedBlockComment));
        test("/*/**/", 0, Err(UnterminatedBlockComment));
        test("/*/**/*/", 8, Ok(true));
        test("/*/**/*/foo", 8, Ok(false));
        test("/**/", 4, Ok(true));
        test("/**/foo", 4, Ok(false));
    }

    #[test]
    fn test_lex_quoted_content() {
        assert_eq!(lex_quoted_content("", '"'), Err(MismatchedQuotes));
        assert_eq!(lex_quoted_content("\"", '"'), Ok(""));
        assert_eq!(lex_quoted_content("\"foo", '"'), Ok("foo"));
        assert_eq!(lex_quoted_content("foo\"bar", '"'), Ok("bar"));
        assert_eq!(lex_quoted_content("foo\"", '"'), Ok(""));
        assert_eq!(lex_quoted_content("foo\\\"", '"'), Err(MismatchedQuotes));
        assert_eq!(lex_quoted_content("foo\\\"bar", '"'), Err(MismatchedQuotes));
        assert_eq!(lex_quoted_content("foo\\\\\"", '"'), Ok(""));
        assert_eq!(lex_quoted_content("foo\\\\\"bar", '"'), Ok("bar"));
        assert_eq!(lex_quoted_content("ab\\\"cd\\\"ef\"yz", '"'), Ok("yz"));
    }

    #[test]
    fn test_find_line_break() {
        assert_eq!(find_line_break(""), 0);
        assert_eq!(find_line_break("\n"), 1);
        assert_eq!(find_line_break("hello"), 5);

        assert_eq!(find_line_break("hello\n"), 6);
        assert_eq!(find_line_break("hello\r"), 6);
        assert_eq!(find_line_break("hello\n\r"), 6);
        assert_eq!(find_line_break("hello\r\n"), 7);

        assert_eq!(find_line_break("hello\nworld"), 6);
        assert_eq!(find_line_break("hello\rworld"), 6);
        assert_eq!(find_line_break("hello\n\rworld"), 6);
        assert_eq!(find_line_break("hello\r\nworld"), 7);
    }
}
