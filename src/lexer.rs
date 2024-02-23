use std::{mem::replace, num::NonZeroUsize};

use thiserror::Error;

use crate::token::{Expect, FixedTokenKind, TokenKind, TokenSet};

#[derive(Debug)]
pub(crate) struct Lexer<'code> {
    code: &'code str,
    pos: usize,
}

impl<'code> Lexer<'code> {
    pub(crate) fn new(code: &'code str) -> Result<Self, LexerError> {
        let mut result = Self { code, pos: 0 };
        result.skip_whitespace()?;
        Ok(result)
    }

    pub(crate) fn pos(&self) -> usize {
        self.pos
    }

    pub(crate) fn next_token(&mut self) -> Result<LexerToken, LexerErrorKind> {
        let rest = &self.code[self.pos..];
        let (kind, len) = if let Some(kind_len) = lex_doc_comment(rest) {
            kind_len
        } else if let Some(kind_len) = lex_integer_or_float(rest) {
            kind_len
        } else if let Some(kind_len) = lex_char_or_label(rest)? {
            kind_len
        } else if let Some(kind_len) = lex_quoted(rest)? {
            kind_len
        } else if let Some(kind_len) = lex_raw_string(rest)? {
            kind_len
        } else if let Some(kind_len) = lex_keyword_or_ident(rest) {
            kind_len
        } else if let Some((kind, len)) = FixedTokenKind::parse_symbol(rest.as_bytes()) {
            (kind.into(), len)
        } else if let Some(kind) = FixedTokenKind::parse_char(rest.as_bytes()[0]) {
            (kind.into(), 1)
        } else {
            return Err(LexerErrorKind::InvalidChar);
        };

        self.pos += len;
        Ok(LexerToken {
            kind,
            len: NonZeroUsize::new(len).expect("token should not be empty"),
        })
    }

    fn skip_whitespace(&mut self) -> Result<(), LexerError> {
        loop {
            let next = lex_whitespace(&self.code[self.pos..]).map_err(|kind| LexerError {
                pos: self.pos,
                kind: kind.into(),
            })?;
            if next == 0 {
                break Ok(());
            }
            self.pos += next;
        }
    }
}

impl Iterator for Lexer<'_> {
    type Item = Result<LexerToken, LexerError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos == self.code.len() {
            return None;
        }

        match self.next_token() {
            Ok(token) => {
                if let Err(error) = self.skip_whitespace() {
                    Some(Err(error))
                } else {
                    Some(Ok(token))
                }
            }
            Err(kind) => Some(Err(LexerError {
                pos: self.pos,
                kind,
            })),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct LexerError {
    pub(crate) pos: usize,
    pub(crate) kind: LexerErrorKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub(crate) enum LexerErrorKind {
    #[error(transparent)]
    Unterminated(#[from] Unterminated),
    #[error("invalid character")]
    InvalidChar,
    #[error("{expect:?} expected, found {found:?}")]
    UnexpectedToken {
        expect: Expect,
        found: Option<TokenKind>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct LexerToken {
    pub(crate) kind: TokenKind,
    pub(crate) len: NonZeroUsize,
}

/// A [`TinyLexer`] that also makes sure the next token matches what is [`Expect`]ed.
#[derive(Debug)]
pub(crate) struct CheckedLexer<'code> {
    lexer: Lexer<'code>,
    current_kind: Option<TokenKind>,
    pos: usize,
    next_token_len: NonZeroUsize,
}

impl<'code> CheckedLexer<'code> {
    pub(crate) fn new(lexer: Lexer<'code>, expect: Expect) -> Result<Self, LexerError> {
        let mut result = Self {
            lexer,
            current_kind: None,
            pos: Default::default(),
            next_token_len: NonZeroUsize::MIN,
        };
        result.next(expect)?; // replace empty current token with actual first token
        Ok(result)
    }

    pub(crate) fn kind(&self) -> TokenKind {
        self.current_kind.expect("current token kind should be set")
    }

    pub(crate) fn pos(&self) -> usize {
        self.pos
    }

    pub(crate) fn matches(&self, tokens: impl Into<TokenSet>) -> bool {
        self.current_kind
            .is_some_and(|kind| tokens.into().contains(kind))
    }

    /// Yields a token from the lexer while also making sure the token afterwards matches `expect`.
    pub(crate) fn next(&mut self, expect: Expect) -> Result<NonZeroUsize, LexerError> {
        self.pos = self.lexer.pos();
        if let Some(next_token) = self.lexer.next() {
            let next_token = next_token?;
            if expect.tokens.contains(next_token.kind) {
                self.current_kind = Some(next_token.kind);
                Ok(replace(&mut self.next_token_len, next_token.len))
            } else {
                Err(LexerError {
                    pos: self.pos,
                    kind: LexerErrorKind::UnexpectedToken {
                        expect,
                        found: Some(next_token.kind),
                    },
                })
            }
        } else if expect.or_end_of_input {
            self.current_kind = None;
            Ok(replace(&mut self.next_token_len, NonZeroUsize::MIN))
        } else {
            Err(LexerError {
                pos: self.pos,
                kind: LexerErrorKind::UnexpectedToken {
                    expect,
                    found: None,
                },
            })
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub(crate) enum Unterminated {
    #[error("unterminated block comment")]
    BlockComment,
    #[error("unterminated string literal")]
    String,
    #[error("unterminated char literal")]
    Char,
}

/// Lexes a doc comment, returning the token kind and the length of the token.
pub(crate) fn lex_doc_comment(rest: &str) -> Option<(TokenKind, usize)> {
    Some((
        TokenKind::DocComment,
        find_line_break(rest.strip_prefix("///")?) + 3,
    ))
}

/// Lexes an integer or float, returning the token kind and the length of the token.
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
pub(crate) fn lex_char_or_label(rest: &str) -> Result<Option<(TokenKind, usize)>, Unterminated> {
    let Some(after_quote) = rest.strip_prefix('\'') else {
        return Ok(None);
    };
    let after_ident_chars =
        after_quote.trim_start_matches(|c: char| c.is_ascii_alphanumeric() || c == '_');
    let ident_chars = after_quote.len() - after_ident_chars.len();
    let quote_after_ident = after_ident_chars.starts_with('\'');
    Ok(if ident_chars < 1 || quote_after_ident {
        let end = lex_quoted_content(after_ident_chars, '\'').ok_or(Unterminated::Char)?;
        Some((TokenKind::Char, rest.len() - end.len()))
    } else {
        Some((TokenKind::Label, rest.len() - after_ident_chars.len()))
    })
}

/// Lexes a quoted string or byte-string/char, returning the token kind and the length of the token.
///
/// Regular chars are handled by [`lex_char_or_label`], since distingushing those is a bit tricky.
pub(crate) fn lex_quoted(rest: &str) -> Result<Option<(TokenKind, usize)>, Unterminated> {
    let (is_char, after_quote) = if let Some(after_quote) = rest.strip_prefix("b'") {
        (true, after_quote)
    } else if let Some(after_quote) = rest.strip_prefix('"').or_else(|| rest.strip_prefix("b\"")) {
        (false, after_quote)
    } else {
        return Ok(None);
    };

    let end =
        lex_quoted_content(after_quote, if is_char { '\'' } else { '"' }).ok_or(if is_char {
            Unterminated::Char
        } else {
            Unterminated::String
        })?;
    Ok(Some((
        if is_char {
            TokenKind::Char
        } else {
            TokenKind::String
        },
        rest.len() - end.len(),
    )))
}

/// Lexes a raw string or byte-string, returning the token kind and the length of the token.
pub(crate) fn lex_raw_string(rest: &str) -> Result<Option<(TokenKind, usize)>, Unterminated> {
    let after_r = if rest.starts_with("r#") || rest.starts_with("r\"") {
        &rest[1..]
    } else if rest.starts_with("br#") || rest.starts_with("br\"") {
        &rest[2..]
    } else {
        return Ok(None);
    };

    let after_pound = after_r.trim_start_matches('#');
    let start_pounds = &after_r[0..after_r.len() - after_pound.len()];
    let mut after_quote = after_pound.strip_prefix('"').ok_or(Unterminated::String)?;
    loop {
        if let Some(end_pounds) = after_quote
            .trim_start_matches(|c: char| c != '"')
            .strip_prefix('"')
        {
            if let Some(end) = end_pounds.strip_prefix(start_pounds) {
                break Ok(Some((TokenKind::String, rest.len() - end.len())));
            }
            after_quote = end_pounds;
        } else {
            break Err(Unterminated::String);
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

/// Returns the number of bytes until non-whitespace or a different kind of whitespace.
///
/// This does not simply skip everything at once, so that error messages can point to e.g. the
/// beginning of an unterminated block comment.
pub(crate) fn lex_whitespace(code: &str) -> Result<usize, Unterminated> {
    match code.bytes().next() {
        Some(c) if c.is_ascii_whitespace() => Ok(code[1..]
            .find(|c: char| !c.is_ascii_whitespace())
            .map_or(code.len(), |len| len + 1)),
        Some(b'/') => {
            if code[1..].starts_with("//") {
                // doc-comments are not considered whitespace
                Ok(0)
            } else if code[1..].starts_with('/') {
                Ok(2 + find_line_break(&code[2..]))
            } else if code[1..].starts_with('*') {
                let start_len = code.len();
                let mut after_block_comment = &code[2..];
                let mut nesting: usize = 0;
                loop {
                    let Some(len) = after_block_comment.find("*/") else {
                        break Err(Unterminated::BlockComment);
                    };
                    if let Some(open) = after_block_comment[..len].find("/*") {
                        after_block_comment = &after_block_comment[open + 2..];
                        nesting += 1;
                    } else {
                        after_block_comment = &after_block_comment[len + 2..];
                        if nesting == 0 {
                            break Ok(start_len - after_block_comment.len());
                        }
                        nesting -= 1;
                    }
                }
            } else {
                Ok(0)
            }
        }
        _ => Ok(0),
    }
}

/// Lexes the contents of something quoted, returning the rest of the string.
fn lex_quoted_content(mut after_quote: &str, end_quote: char) -> Option<&str> {
    loop {
        let quote_or_backslash =
            after_quote.trim_start_matches(|c: char| c != end_quote && c != '\\');
        if quote_or_backslash.is_empty() {
            return None;
        }
        if let Some(end) = quote_or_backslash.strip_prefix(end_quote) {
            break Some(end);
        }
        let Some(after_escape) = quote_or_backslash.get(2..) else {
            return None;
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
    fn test_lex_doc_comment() {
        assert_eq!(lex_doc_comment(""), None);
        assert_eq!(lex_doc_comment("not a doc comment"), None);
        assert_eq!(lex_doc_comment("// normal comment"), None);

        assert_eq!(lex_doc_comment("/// foo"), Some((TokenKind::DocComment, 7)));
        assert_eq!(lex_doc_comment("///\na"), Some((TokenKind::DocComment, 4)));
    }

    #[test]
    fn test_lex_integer_or_float() {
        assert_eq!(lex_integer_or_float(""), None);
        assert_eq!(lex_integer_or_float("not a number"), None);

        assert_eq!(lex_integer_or_float("123"), Some((TokenKind::Integer, 3)));
        assert_eq!(lex_integer_or_float("0xFF"), Some((TokenKind::Integer, 4)));
        assert_eq!(lex_integer_or_float("0b101"), Some((TokenKind::Integer, 5)));
        assert_eq!(lex_integer_or_float("0o777"), Some((TokenKind::Integer, 5)));

        assert_eq!(lex_integer_or_float("42.0"), Some((TokenKind::Float, 4)));
        assert_eq!(lex_integer_or_float("42E3"), Some((TokenKind::Float, 4)));
        assert_eq!(lex_integer_or_float("10E+3"), Some((TokenKind::Float, 5)));
        assert_eq!(lex_integer_or_float("10E-3"), Some((TokenKind::Float, 5)));
    }

    #[test]
    fn test_lex_char_or_label() {
        assert_eq!(lex_char_or_label(""), Ok(None));
        assert_eq!(lex_char_or_label("a"), Ok(None));
        assert_eq!(lex_char_or_label("'"), Err(Unterminated::Char));
        assert_eq!(lex_char_or_label("'?"), Err(Unterminated::Char));
        assert_eq!(lex_char_or_label("'?'"), Ok(Some((TokenKind::Char, 3))));
        assert_eq!(lex_char_or_label("''"), Ok(Some((TokenKind::Char, 2))));
        assert_eq!(lex_char_or_label("'a"), Ok(Some((TokenKind::Label, 2))));
        assert_eq!(lex_char_or_label("'a'"), Ok(Some((TokenKind::Char, 3))));
        assert_eq!(lex_char_or_label("'ab"), Ok(Some((TokenKind::Label, 3))));
        assert_eq!(lex_char_or_label("'ab'"), Ok(Some((TokenKind::Char, 4))));
    }

    #[test]
    fn test_lex_quoted() {
        assert_eq!(lex_quoted(""), Ok(None));
        assert_eq!(lex_quoted("a"), Ok(None));
        assert_eq!(lex_quoted("\""), Err(Unterminated::String));
        assert_eq!(lex_quoted("\"\""), Ok(Some((TokenKind::String, 2))));
        assert_eq!(lex_quoted("\"\"foo"), Ok(Some((TokenKind::String, 2))));
        assert_eq!(lex_quoted("\"\"\""), Ok(Some((TokenKind::String, 2))));
        assert_eq!(lex_quoted("\"nice\""), Ok(Some((TokenKind::String, 6))));
        assert_eq!(lex_quoted("\"nice\"foo"), Ok(Some((TokenKind::String, 6))));
        assert_eq!(lex_quoted("\"\\\""), Err(Unterminated::String));
        assert_eq!(lex_quoted("\"\\\"\""), Ok(Some((TokenKind::String, 4))));
        assert_eq!(lex_quoted("\"\\\"\"foo"), Ok(Some((TokenKind::String, 4))));
        assert_eq!(lex_quoted("\"\\\\\""), Ok(Some((TokenKind::String, 4))));
        assert_eq!(lex_quoted("\"\\\\\"foo"), Ok(Some((TokenKind::String, 4))));

        assert_eq!(lex_quoted("b\"bytes\""), Ok(Some((TokenKind::String, 8))));
        assert_eq!(lex_quoted("b\"bytes"), Err(Unterminated::String));
        assert_eq!(lex_quoted("b'X'"), Ok(Some((TokenKind::Char, 4))));
        assert_eq!(lex_quoted("b'X"), Err(Unterminated::Char));

        assert_eq!(lex_quoted("b'\"'"), Ok(Some((TokenKind::Char, 4))));
        assert_eq!(lex_quoted("\"'\""), Ok(Some((TokenKind::String, 3))));
    }

    #[test]
    fn test_lex_raw_string() {
        assert_eq!(lex_raw_string(""), Ok(None));
        assert_eq!(lex_raw_string("a"), Ok(None));

        assert_eq!(lex_raw_string("r"), Ok(None));
        assert_eq!(lex_raw_string("r\""), Err(Unterminated::String));
        assert_eq!(lex_raw_string("r#\""), Err(Unterminated::String));
        assert_eq!(lex_raw_string("r###\""), Err(Unterminated::String));
        assert_eq!(lex_raw_string("rb"), Ok(None));
        assert_eq!(lex_raw_string("rb\""), Ok(None));

        assert_eq!(lex_raw_string("b"), Ok(None));
        assert_eq!(lex_raw_string("br"), Ok(None));
        assert_eq!(lex_raw_string("br\""), Err(Unterminated::String));
        assert_eq!(lex_raw_string("br#\""), Err(Unterminated::String));
        assert_eq!(lex_raw_string("br###\""), Err(Unterminated::String));

        assert_eq!(lex_raw_string("r\"foo\""), Ok(Some((TokenKind::String, 6))));
        assert_eq!(
            lex_raw_string("r\"foo\"bar\""),
            Ok(Some((TokenKind::String, 6)))
        );
        assert_eq!(
            lex_raw_string("r#\"foo\"bar\"#"),
            Ok(Some((TokenKind::String, 12)))
        );
        assert_eq!(
            lex_raw_string("r###\"foo\"##bar\"###"),
            Ok(Some((TokenKind::String, 18)))
        );
        assert_eq!(
            lex_raw_string("r###\"foo\"##bar\"####"),
            Ok(Some((TokenKind::String, 18)))
        );
    }

    #[test]
    fn test_lex_keyword_or_ident() {
        assert_eq!(lex_keyword_or_ident(""), None);
        assert_eq!(lex_keyword_or_ident("42"), None);
        assert_eq!(lex_keyword_or_ident("42foo"), None);
        assert_eq!(lex_keyword_or_ident("."), None);

        assert_eq!(lex_keyword_or_ident("fn"), Some((TokenKind::Fn, 2)));
        assert_eq!(lex_keyword_or_ident("_"), Some((TokenKind::Underscore, 1)));

        assert_eq!(lex_keyword_or_ident("foo"), Some((TokenKind::Ident, 3)));
        assert_eq!(lex_keyword_or_ident("foo42"), Some((TokenKind::Ident, 5)));
        assert_eq!(lex_keyword_or_ident("_foo"), Some((TokenKind::Ident, 4)));
        assert_eq!(lex_keyword_or_ident("_42"), Some((TokenKind::Ident, 3)));
        assert_eq!(lex_keyword_or_ident("_42foo"), Some((TokenKind::Ident, 6)));
        assert_eq!(lex_keyword_or_ident("_foo42"), Some((TokenKind::Ident, 6)));
    }

    #[test]
    fn test_trim_whitespace() {
        assert_eq!(lex_whitespace(""), Ok(0));
        assert_eq!(lex_whitespace("foo"), Ok(0));
        assert_eq!(lex_whitespace(" \n\t"), Ok(3));
        assert_eq!(lex_whitespace(" \n\tfoo"), Ok(3));
        assert_eq!(lex_whitespace("// foo"), Ok(6));
        assert_eq!(lex_whitespace("// foo\n"), Ok(7));
        assert_eq!(lex_whitespace("// foo\nbar"), Ok(7));
        assert_eq!(lex_whitespace("// foo\n "), Ok(7));
        assert_eq!(lex_whitespace("/// foo"), Ok(0));
        assert_eq!(lex_whitespace("/*foo bar*/"), Ok(11));
        assert_eq!(lex_whitespace("/*foo bar*/bar"), Ok(11));
        assert_eq!(lex_whitespace("/*foo bar*/ "), Ok(11));
        assert_eq!(lex_whitespace("/*/"), Err(Unterminated::BlockComment));
        assert_eq!(lex_whitespace("/*/**/"), Err(Unterminated::BlockComment));
        assert_eq!(lex_whitespace("/*/**/*/"), Ok(8));
        assert_eq!(lex_whitespace("/*/**/*/foo"), Ok(8));
        assert_eq!(lex_whitespace("/**/"), Ok(4));
        assert_eq!(lex_whitespace("/**/foo"), Ok(4));
    }

    #[test]
    fn test_lex_quoted_content() {
        assert_eq!(lex_quoted_content("", '"'), None);
        assert_eq!(lex_quoted_content("\"", '"'), Some(""));
        assert_eq!(lex_quoted_content("\"foo", '"'), Some("foo"));
        assert_eq!(lex_quoted_content("foo\"bar", '"'), Some("bar"));
        assert_eq!(lex_quoted_content("foo\"", '"'), Some(""));
        assert_eq!(lex_quoted_content("foo\\\"", '"'), None);
        assert_eq!(lex_quoted_content("foo\\\"bar", '"'), None);
        assert_eq!(lex_quoted_content("foo\\\\\"", '"'), Some(""));
        assert_eq!(lex_quoted_content("foo\\\\\"bar", '"'), Some("bar"));
        assert_eq!(lex_quoted_content("ab\\\"cd\\\"ef\"yz", '"'), Some("yz"));
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
