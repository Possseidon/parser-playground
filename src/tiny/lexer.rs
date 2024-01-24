use std::mem::{replace, take};

use smol_str::SmolStr;

use crate::{
    lexer::{find_line_break, lex_quoted, lex_raw_string},
    token::{Expect, FixedTokenKind, TokenKind, TokenSet},
};

use super::{TinyError, TinyResult};

#[derive(Debug)]
pub(crate) struct TinyLexer<'code> {
    code: &'code str,
    pos: usize,
}

impl<'code> TinyLexer<'code> {
    pub(crate) fn new(code: &'code str) -> Self {
        Self { code, pos: 0 }
    }

    /// Yields the next token, assuming [`Self::skip_whitespace()`] was called previously.
    pub(crate) fn next_token(&mut self) -> TinyResult<TinyLexerToken> {
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
                let end = lex_quoted(after_ident_chars, '\'').ok_or(TinyError)?;
                (TokenKind::Char, rest.len() - end.len(), true)
            } else {
                (TokenKind::Label, rest.len() - after_ident_chars.len(), true)
            }
        } else if let Some(after_quote) = rest.strip_prefix("b'") {
            let end = lex_quoted(after_quote, '\'').ok_or(TinyError)?;
            (TokenKind::Char, rest.len() - end.len(), true)
        } else if let Some(after_quote) = rest.strip_prefix('"') {
            let end = lex_quoted(after_quote, '\"').ok_or(TinyError)?;
            (TokenKind::String, rest.len() - end.len(), true)
        } else if let Some(after_quote) = rest.strip_prefix("b\"") {
            let end = lex_quoted(after_quote, '\"').ok_or(TinyError)?;
            (TokenKind::String, rest.len() - end.len(), true)
        } else if rest.starts_with("r#") || rest.starts_with("r\"") {
            let end = lex_raw_string(&rest[1..]).ok_or(TinyError)?;
            (TokenKind::String, rest.len() - end.len(), true)
        } else if rest.starts_with("br#") || rest.starts_with("br\"") {
            let end = lex_raw_string(&rest[2..]).ok_or(TinyError)?;
            (TokenKind::String, rest.len() - end.len(), true)
        } else if rest.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') {
            let ident_len = rest
                .find(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                .unwrap_or(rest.len());
            if let Some(keyword) = FixedTokenKind::parse_keyword(rest[..ident_len].as_bytes()) {
                (keyword.into(), ident_len, false)
            } else {
                (TokenKind::Ident, ident_len, true)
            }
        } else if let Some((symbol, len)) = FixedTokenKind::parse_symbol(rest.as_bytes()) {
            (symbol.into(), len, false)
        } else {
            let kind = FixedTokenKind::parse_char(rest.as_bytes()[0]).ok_or(TinyError)?;
            (kind.into(), 1, false)
        };

        self.pos += len;
        Ok(TinyLexerToken {
            kind,
            text: if dynamic {
                rest[..len].into()
            } else {
                SmolStr::default()
            },
        })
    }

    /// Skips over whitespace, and returns [`None`] if EOF was reached.
    pub(crate) fn skip_whitespace(&mut self) -> Option<TinyResult<()>> {
        loop {
            match self.code[self.pos..].bytes().next() {
                None => break None,
                Some(c) if c.is_ascii_whitespace() => {
                    self.pos = self.code[self.pos + 1..]
                        .find(|c: char| !c.is_ascii_whitespace())
                        .map_or(self.code.len(), |len| self.pos + len + 1);
                }
                Some(b'/') => {
                    if self.code[self.pos + 1..].starts_with("//") {
                        break Some(Ok(()));
                    } else if self.code[self.pos + 1..].starts_with('/') {
                        self.pos += 2 + find_line_break(&self.code[self.pos + 2..]);
                    } else if self.code[self.pos + 1..].starts_with('*') {
                        let start_len = self.code[self.pos..].len();
                        let mut after_block_comment = &self.code[self.pos + 2..];
                        let mut nesting: usize = 0;
                        loop {
                            let Some(len) = after_block_comment.find("*/") else {
                                return Some(Err(TinyError));
                            };
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
                        break Some(Ok(()));
                    }
                }
                _ => break Some(Ok(())),
            }
        }
    }
}

impl Iterator for TinyLexer<'_> {
    type Item = TinyResult<TinyLexerToken>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.skip_whitespace()?.and_then(|_| self.next_token()))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TinyLexerToken {
    pub(crate) kind: TokenKind,
    pub(crate) text: SmolStr,
}

pub(crate) trait TinyTokenStream: Iterator<Item = TinyResult<TinyLexerToken>> {}

impl<T: Iterator<Item = TinyResult<TinyLexerToken>>> TinyTokenStream for T {}

/// A [`TinyTokenStream`] that also makes sure the next token matches what is [`Expect`]ed.
#[derive(Debug)]
pub(crate) struct CheckedTinyTokenStream<T: TinyTokenStream> {
    pub(crate) token_stream: T,
    pub(crate) current_kind: Option<TokenKind>,
    pub(crate) next_token: SmolStr,
}

impl<T: TinyTokenStream> CheckedTinyTokenStream<T> {
    pub(crate) fn new(token_stream: T, expect: Expect) -> TinyResult<Self> {
        let mut result = Self {
            token_stream,
            current_kind: None,
            next_token: SmolStr::default(),
        };
        result.next(expect)?; // replace empty current token with actual first token
        Ok(result)
    }

    pub(crate) fn kind(&self) -> TokenKind {
        self.current_kind.expect("token kind should be set")
    }

    pub(crate) fn matches(&self, tokens: TokenSet) -> bool {
        self.current_kind.is_some_and(|kind| tokens.contains(kind))
    }

    /// Yields a token from the stream while also making sure the token afterwards matches `expect`.
    pub(crate) fn next(&mut self, expect: Expect) -> TinyResult<SmolStr> {
        if let Some(next_token) = self.token_stream.next() {
            let next_token = next_token?;
            if expect.tokens.contains(next_token.kind) {
                self.current_kind = Some(next_token.kind);
                Ok(replace(&mut self.next_token, next_token.text))
            } else {
                Err(TinyError)
            }
        } else if expect.or_end_of_input {
            self.current_kind = None;
            Ok(take(&mut self.next_token))
        } else {
            Err(TinyError)
        }
    }
}
