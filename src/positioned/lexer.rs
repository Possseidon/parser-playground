use std::num::NonZeroUsize;

use thiserror::Error;

use crate::{
    lexer::{
        lex_char_or_label, lex_doc_comment, lex_integer_or_float, lex_keyword_or_ident, lex_quoted,
        lex_raw_string, trim_whitespace, LexerToken, Unterminated,
    },
    token::{Expect, FixedTokenKind, Positioned, TokenKind},
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

    pub(crate) fn pos(&self) -> usize {
        self.pos
    }

    pub(crate) fn next_token(&mut self) -> Result<LexerToken<Positioned>, LexerError> {
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

        self.pos += len;
        Ok(LexerToken {
            kind,
            token: NonZeroUsize::new(len).expect("token should not be empty"),
        })
    }
}

impl Iterator for PositionedLexer<'_> {
    type Item = Result<LexerToken<Positioned>, PositionedLexerError>;

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
pub(crate) struct TokenSpan {
    pub(crate) pos: usize,
    pub(crate) len: NonZeroUsize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OptionalTokenSpan {
    Some(TokenSpan),
    None { pos: usize },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PositionedLexerError {
    pub(crate) pos: usize,
    pub(crate) kind: LexerError,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub(crate) enum LexerError {
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
