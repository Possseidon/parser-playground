use std::{mem::replace, num::NonZeroUsize};

use thiserror::Error;

use crate::{
    lexer::{
        lex_char_or_label, lex_doc_comment, lex_integer_or_float, lex_keyword_or_ident, lex_quoted,
        lex_raw_string, trim_whitespace, Unterminated,
    },
    token::{Expect, FixedTokenKind, TokenKind, TokenSet},
};

#[derive(Debug)]
pub(crate) struct PositionedLexer<'code> {
    code: &'code str,
    pos: usize,
}

impl<'code> PositionedLexer<'code> {
    pub(crate) fn new(code: &'code str) -> Self {
        Self { code, pos: 0 }
    }

    pub(crate) fn next_token(&mut self) -> Result<PositionedLexerToken, LexerError> {
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
            return Err(LexerError::InvalidChar);
        };

        let span = TokenSpan {
            pos: self.pos,
            len: NonZeroUsize::new(len).expect("token should not be empty"),
        };

        self.pos += len;
        Ok(PositionedLexerToken { kind, span })
    }
}

impl Iterator for PositionedLexer<'_> {
    type Item = Result<PositionedLexerToken, PositionedLexerError>;

    fn next(&mut self) -> Option<Self::Item> {
        let pos = self.pos;
        match trim_whitespace(self.code) {
            Ok(rest) => (!rest.is_empty()).then(|| {
                self.pos += self.code.len() - rest.len();
                self.next_token().map_err(|kind| {
                    self.pos = self.code.len();
                    PositionedLexerError { pos, kind }
                })
            }),
            Err(kind) => {
                self.pos = self.code.len();
                Some(Err(PositionedLexerError {
                    pos,
                    kind: LexerError::Unterminated(kind),
                }))
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PositionedLexerToken {
    span: TokenSpan,
    kind: TokenKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TokenSpan {
    pos: usize,
    len: NonZeroUsize,
}

#[derive(Debug)]
pub(crate) struct CheckedPositionedLexer<'code> {
    lexer: PositionedLexer<'code>,
    current_kind: Option<TokenKind>,
    next_token: TokenSpan,
}

impl<'code> CheckedPositionedLexer<'code> {
    pub(crate) fn new(
        lexer: PositionedLexer<'code>,
        expect: Expect,
    ) -> Result<Self, PositionedLexerError> {
        let mut result = Self {
            lexer,
            // arbitrary current_kind and next_token; both will be replaced immediately
            current_kind: None,
            next_token: TokenSpan {
                pos: 0,
                len: NonZeroUsize::MIN,
            },
        };
        result.next(expect)?;
        Ok(result)
    }

    pub(crate) fn kind(&self) -> TokenKind {
        self.current_kind.expect("token kind should be set")
    }

    pub(crate) fn matches(&self, tokens: TokenSet) -> bool {
        self.current_kind.is_some_and(|kind| tokens.contains(kind))
    }

    /// Yields a token from the stream while also making sure the token afterwards matches `expect`.
    pub(crate) fn next(&mut self, expect: Expect) -> Result<TokenSpan, PositionedLexerError> {
        if let Some(next_token) = self.lexer.next() {
            let next_token = next_token?;
            if expect.tokens.contains(next_token.kind) {
                self.current_kind = Some(next_token.kind);
                Ok(replace(&mut self.next_token, next_token.span))
            } else {
                Err(PositionedLexerError {
                    pos: next_token.span.pos,
                    kind: LexerError::UnexpectedToken {
                        expected: expect,
                        found: Some(next_token.kind),
                    },
                })
            }
        } else if expect.or_end_of_input {
            self.current_kind = None;
            // will never be read again
            Ok(self.next_token)
        } else {
            Err(PositionedLexerError {
                pos: self.lexer.pos,
                kind: LexerError::UnexpectedToken {
                    expected: expect,
                    found: None,
                },
            })
        }
    }
}

pub(crate) struct PositionedLexerError {
    pub(crate) pos: usize,
    pub(crate) kind: LexerError,
}

#[derive(Debug, Error)]
pub(crate) enum LexerError {
    #[error(transparent)]
    Unterminated(#[from] Unterminated),
    #[error("invalid character")]
    InvalidChar,
    #[error("{expected:?} expected, found {found:?}")]
    UnexpectedToken {
        expected: Expect,
        found: Option<TokenKind>,
    },
}
