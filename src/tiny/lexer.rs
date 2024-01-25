use std::mem::{replace, take};

use smol_str::SmolStr;

use crate::{
    lexer::{
        lex_char_or_label, lex_doc_comment, lex_integer_or_float, lex_keyword_or_ident, lex_quoted,
        lex_raw_string, lex_whitespace, UnterminatedBlockComment,
    },
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

        let (kind, len) = if let Some(kind_len) = lex_doc_comment(rest) {
            kind_len
        } else if let Some(kind_len) = lex_integer_or_float(rest) {
            kind_len
        } else if let Some(kind_len) = lex_char_or_label(rest).map_err(|_| TinyError)? {
            kind_len
        } else if let Some(kind_len) = lex_quoted(rest).map_err(|_| TinyError)? {
            kind_len
        } else if let Some(kind_len) = lex_raw_string(rest).map_err(|_| TinyError)? {
            kind_len
        } else if let Some(kind_len) = lex_keyword_or_ident(rest) {
            kind_len
        } else if let Some((kind, len)) = FixedTokenKind::parse_symbol(rest.as_bytes()) {
            (kind.into(), len)
        } else if let Some(kind) = FixedTokenKind::parse_char(rest.as_bytes()[0]) {
            (kind.into(), 1)
        } else {
            return Err(TinyError);
        };

        self.pos += len;
        Ok(TinyLexerToken {
            kind,
            text: if kind.is_dynamic() {
                rest[..len].into()
            } else {
                SmolStr::default()
            },
        })
    }
}

impl Iterator for TinyLexer<'_> {
    type Item = TinyResult<TinyLexerToken>;

    fn next(&mut self) -> Option<Self::Item> {
        match lex_whitespace(self.code, &mut self.pos) {
            Ok(eof) => (!eof).then(|| self.next_token()),
            Err(UnterminatedBlockComment) => Some(Err(TinyError)),
        }
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
