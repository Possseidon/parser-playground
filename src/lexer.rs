use std::{
    mem::{replace, take},
    num::NonZeroUsize,
};

use smol_str::SmolStr;

use crate::token::{Expect, TokenKind, TokenSet};

pub(crate) struct TinyLexerToken {
    pub(crate) kind: TokenKind,
    pub(crate) text: SmolStr,
}

type TinyLexerTokenResult = Result<TinyLexerToken, FatalLexerError>;

pub(crate) trait TinyTokenStream: Iterator<Item = TinyLexerTokenResult> {}
impl<T: Iterator<Item = TinyLexerTokenResult>> TinyTokenStream for T {}

/// A [`TinyTokenStream`] that also makes sure the next token matches what is [`Expect`]ed.
#[derive(Debug)]
pub(crate) struct CheckedTinyTokenStream<T: TinyTokenStream> {
    token_stream: T,
    current_kind: Option<TokenKind>,
    next_token: SmolStr,
}

impl<T: TinyTokenStream> CheckedTinyTokenStream<T> {
    pub(crate) fn new(token_stream: T, expect: Expect) -> Result<Self, FatalLexerError> {
        let mut result = Self {
            token_stream,
            current_kind: None,
            next_token: SmolStr::new_inline(""),
        };
        result.next(expect)?; // replace empty current token with actual first token
        Ok(result)
    }

    pub(crate) fn kind(&self) -> TokenKind {
        self.current_kind.expect("token kind should be set")
    }

    pub(crate) fn matches(&self, tokens: TokenSet) -> bool {
        tokens.contains(self.kind())
    }

    /// Yields a token from the stream while also making sure the token afterwards matches `expect`.
    pub(crate) fn next(&mut self, expect: Expect) -> Result<SmolStr, FatalLexerError> {
        if let Some(next_token) = self.token_stream.next() {
            let next_token = next_token?;
            if expect.tokens.contains(next_token.kind) {
                self.current_kind = Some(next_token.kind);
                Ok(replace(&mut self.next_token, next_token.text))
            } else {
                Err(FatalLexerError)
            }
        } else if expect.or_end_of_input {
            self.current_kind = None;
            Ok(take(&mut self.next_token))
        } else {
            Err(FatalLexerError)
        }
    }
}

#[derive(Debug)]
pub(crate) struct TinyLexer<'code> {
    code: &'code str,
    pos: usize,
}

impl<'code> TinyLexer<'code> {
    pub(crate) fn new(code: &'code str) -> Self {
        Self { code, pos: 0 }
    }

    /// After and error is yielded, all consecutive calls will also yield an error.
    fn next_transposed(&mut self) -> Result<Option<TinyLexerToken>, FatalLexerError> {
        if self.eof_after_whitespace()? {
            return Ok(None);
        }

        let rest = &self.code[self.pos..];
        let (kind, len, dynamic) = if let Some(after_doc_comment) = rest.strip_prefix("///") {
            (
                TokenKind::DocComment,
                find_line_break(after_doc_comment) + 3,
                true,
            )
        } else if let Some(after_initial_digit) = rest.strip_prefix(|c: char| c.is_ascii_digit()) {
            if let Some(after_base) =
                after_initial_digit.strip_prefix(['B', 'b', 'O', 'o', 'X', 'x'])
            {
                let end =
                    after_base.trim_start_matches(|c: char| c.is_ascii_alphanumeric() || c == '_');
                (TokenKind::Integer, rest.len() - end.len(), true)
            } else {
                let mut token_kind = TokenKind::Integer;
                let mut after_digits = after_initial_digit
                    .trim_start_matches(|c: char| c.is_ascii_digit() || c == '_');

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

                let end = after_digits
                    .trim_start_matches(|c: char| c.is_ascii_alphanumeric() || c == '_');

                (token_kind, rest.len() - end.len(), true)
            }
        } else if let Some(after_quote) = rest.strip_prefix('\'') {
            // Implementing label detection can be kindof hard to wrap your head around.

            // Examples for valid chars and labels:

            // input | ident | ' after
            //       | chars | ident
            // ------+-------+--------
            // ''    |     0 | true
            // 'a'   |     1 | true
            // 'ab'  |     2 | true
            // '?'   |     0 | false
            // ------+-------+--------
            // 'a    |     1 | false
            // 'ab   |     2 | false

            // Truth table based on the examples above:

            //   | true | false
            // --+------+------
            // 0 | char | char
            // 1 | char | label
            // 2 | char | label

            // Reading from the truth table:
            // is_char = (ident chars) < 1 || (' after ident)

            let after_ident_chars =
                after_quote.trim_start_matches(|c: char| c.is_ascii_alphanumeric() || c == '_');

            let ident_chars = after_quote.len() - after_ident_chars.len();
            let quote_after_ident = after_ident_chars.starts_with('\'');

            if ident_chars < 1 || quote_after_ident {
                let end = lex_quoted(after_ident_chars, '\'', FatalLexerError)?;
                (TokenKind::Char, rest.len() - end.len(), true)
            } else {
                (TokenKind::Label, rest.len() - after_ident_chars.len(), true)
            }
        } else if let Some(after_quote) = rest.strip_prefix("b'") {
            let end = lex_quoted(after_quote, '\'', FatalLexerError)?;
            (TokenKind::Char, rest.len() - end.len(), true)
        } else if let Some(after_quote) = rest.strip_prefix('"') {
            let end = lex_quoted(after_quote, '\"', FatalLexerError)?;
            (TokenKind::String, rest.len() - end.len(), true)
        } else if let Some(after_quote) = rest.strip_prefix("b\"") {
            let end = lex_quoted(after_quote, '\"', FatalLexerError)?;
            (TokenKind::String, rest.len() - end.len(), true)
        } else if rest.starts_with("r#") || rest.starts_with("r\"") {
            let end = lex_raw_string(&rest[1..])?;
            (TokenKind::String, rest.len() - end.len(), true)
        } else if rest.starts_with("br#") || rest.starts_with("br\"") {
            let end = lex_raw_string(&rest[2..])?;
            (TokenKind::String, rest.len() - end.len(), true)
        } else if rest.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') {
            let ident_len = rest
                .find(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                .unwrap_or(rest.len());
            if let Some(keyword) = TokenKind::parse_keyword(rest[..ident_len].as_bytes()) {
                (keyword, ident_len, false)
            } else {
                (TokenKind::Ident, ident_len, true)
            }
        } else if let Some((symbol, len)) = TokenKind::parse_symbol(rest.as_bytes()) {
            (symbol, len, false)
        } else {
            let kind = TokenKind::parse_char(rest.as_bytes()[0]).ok_or(FatalLexerError)?;
            (kind, 1, false)
        };

        self.pos += len;
        Ok(Some(TinyLexerToken {
            kind,
            text: if dynamic {
                rest[..len].into()
            } else {
                SmolStr::new_inline("")
            },
        }))
    }

    fn eof_after_whitespace(&mut self) -> Result<bool, FatalLexerError> {
        loop {
            match self.code[self.pos..].bytes().next() {
                None => break Ok(true),
                Some(c) if c.is_ascii_whitespace() => {
                    self.pos = self.code[self.pos + 1..]
                        .find(|c: char| !c.is_ascii_whitespace())
                        .map_or(self.code.len(), |len| self.pos + len + 1);
                }
                Some(b'/') => {
                    if self.code[self.pos + 1..].starts_with("//") {
                        break Ok(false);
                    } else if self.code[self.pos + 1..].starts_with('/') {
                        self.pos = 2 + find_line_break(&self.code[self.pos + 2..]);
                    } else if self.code[self.pos + 1..].starts_with('*') {
                        let start_len = self.code[self.pos..].len();
                        let mut after_block_comment = &self.code[self.pos + 2..];
                        let mut nesting: usize = 0;
                        loop {
                            let len = after_block_comment.find("*/").ok_or(FatalLexerError)?;
                            if let Some(open) = after_block_comment[..len].find("/*") {
                                after_block_comment = &after_block_comment[open + 2..];
                                nesting += 1;
                            } else {
                                after_block_comment = &after_block_comment[len + 2..];
                                if nesting == 0 {
                                    self.pos += start_len - after_block_comment.len();
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
}

fn find_line_break(text: &str) -> usize {
    let line_break = text
        .bytes()
        .enumerate()
        .find_map(|(line, byte)| [b'\n', b'\r'].contains(&byte).then_some(line))
        .unwrap_or(text.len());

    match text.as_bytes().get(line_break + 1) {
        Some(b'\n') => line_break + 1,
        _ => line_break,
    }
}

fn lex_quoted<E>(mut after_quote: &str, quote: char, unterminated_error: E) -> Result<&str, E> {
    loop {
        after_quote = after_quote.trim_start_matches(|c: char| c != quote && c != '\\');
        if let Some(end) = after_quote.strip_prefix(quote) {
            break Ok(end);
        }
        after_quote = match after_quote
            .trim_start_matches(|c: char| c != '\\')
            .strip_prefix(|_| true)
        {
            Some(after_escape) => after_escape,
            None => return Err(unterminated_error),
        };
    }
}

fn lex_raw_string(after_r: &str) -> Result<&str, FatalLexerError> {
    let after_pound = after_r.trim_matches('#');
    let start_pounds = &after_r[0..(after_r.len() - after_pound.len())];
    let mut after_quote = after_pound.strip_prefix('"').unwrap_or(after_pound);
    loop {
        after_quote = after_quote.trim_start_matches(|c: char| c != '"');
        if let Some(end_pounds) = after_quote.strip_prefix('"') {
            if let Some(end) = end_pounds.strip_prefix(start_pounds) {
                break Ok(end);
            }
            after_quote = end_pounds;
        } else {
            break Err(FatalLexerError);
        }
    }
}

/// Some error occured during tiny lexing.
///
/// Always fatal; afterwards the iterator will be empty and yield `None`.
///
/// [`TinyLexer`] cannot simply return [`None`] in case of error, since it needs to be
/// distinguishable from a plain end of input.
#[derive(Debug)]
pub(crate) struct FatalLexerError;

impl Iterator for TinyLexer<'_> {
    type Item = TinyLexerTokenResult;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_transposed().transpose()
    }
}

pub(crate) struct PositionedLexer<'code> {
    code: &'code str,
    pos: usize,
    errors: Vec<LexerError>,
    next: Option<(TokenKind, PositionedLexerToken)>,
}

impl<'code> PositionedLexer<'code> {
    /// To figure out initally skipped whitespace, simply call [`Self::pos()`] immediately.
    pub(crate) fn new(code: &'code str) -> Self {
        let mut result = Self {
            code,
            pos: 0,
            errors: Vec::new(),
            next: None,
        };
        result.advance();
        result
    }

    pub(crate) fn pos(&self) -> usize {
        self.pos
    }

    /// Peeks the kind of the next token.
    pub(crate) fn peek_expected(&self) -> TokenKind {
        self.peek().expect("peeked token should be expected")
    }

    /// Peeks the kind of the next token.
    pub(crate) fn peek(&self) -> Option<TokenKind> {
        self.next.map(|(kind, _)| kind)
    }

    pub(crate) fn next_expected(&mut self) -> PositionedLexerToken {
        self.next().expect("next token should be expected")
    }

    /// Automatically pushes all encountered errors into [`Self::errors`].
    ///
    /// Automatically skips over whitespace, which is included in the next token.
    fn advance(&mut self) {
        todo!()
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct PositionedLexerToken {
    pub(crate) pos: usize,
    pub(crate) len: NonZeroUsize,
    pub(crate) trailing_whitespace_len: usize,
}

enum LexerErrorKind {}

/// Some error occured during lexing.
pub(crate) struct LexerError {
    kind: LexerErrorKind,
    from: usize,
    to: usize,
}

impl Iterator for PositionedLexer<'_> {
    type Item = PositionedLexerToken;

    fn next(&mut self) -> Option<Self::Item> {
        let Some((_, token)) = self.next.take() else {
            return None;
        };
        self.advance();
        Some(token)
    }
}
