use std::mem::{replace, take};

use smol_str::SmolStr;

use crate::{
    lexer::{
        lex_char_or_label, lex_doc_comment, lex_integer_or_float, lex_keyword_or_ident, lex_quoted,
        lex_raw_string, trim_whitespace,
    },
    token::{Expect, FixedTokenKind, TokenKind, TokenSet},
};

use super::{TinyError, TinyResult};

#[derive(Debug)]
pub(crate) struct TinyLexer<'code> {
    code: &'code str,
}

impl<'code> TinyLexer<'code> {
    pub(crate) fn new(code: &'code str) -> Self {
        Self { code }
    }

    /// Yields the next token, assuming whitespace was skipped already.
    pub(crate) fn next_token(&mut self) -> TinyResult<TinyLexerToken> {
        let (kind, len) = if let Some(kind_len) = lex_doc_comment(self.code) {
            kind_len
        } else if let Some(kind_len) = lex_integer_or_float(self.code) {
            kind_len
        } else if let Some(kind_len) = lex_char_or_label(self.code).map_err(|_| TinyError)? {
            kind_len
        } else if let Some(kind_len) = lex_quoted(self.code).map_err(|_| TinyError)? {
            kind_len
        } else if let Some(kind_len) = lex_raw_string(self.code).map_err(|_| TinyError)? {
            kind_len
        } else if let Some(kind_len) = lex_keyword_or_ident(self.code) {
            kind_len
        } else if let Some((kind, len)) = FixedTokenKind::parse_symbol(self.code.as_bytes()) {
            (kind.into(), len)
        } else if let Some(kind) = FixedTokenKind::parse_char(self.code.as_bytes()[0]) {
            (kind.into(), 1)
        } else {
            return Err(TinyError);
        };

        let text = if kind.is_dynamic() {
            self.code[..len].into()
        } else {
            SmolStr::default()
        };

        self.code = &self.code[len..];
        Ok(TinyLexerToken { kind, text })
    }
}

impl<'code> From<&'code str> for TinyLexer<'code> {
    fn from(code: &'code str) -> Self {
        Self::new(code)
    }
}

impl Iterator for TinyLexer<'_> {
    type Item = TinyResult<TinyLexerToken>;

    fn next(&mut self) -> Option<Self::Item> {
        match trim_whitespace(self.code) {
            Ok(rest) => {
                self.code = rest;
                (!self.code.is_empty()).then(|| self.next_token())
            }
            Err(_) => {
                self.code = "";
                Some(Err(TinyError))
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TinyLexerToken {
    kind: TokenKind,
    text: SmolStr,
}

/// A [`TinyLexer`] that also makes sure the next token matches what is [`Expect`]ed.
#[derive(Debug)]
pub(crate) struct CheckedTinyLexer<'code> {
    lexer: TinyLexer<'code>,
    current_kind: Option<TokenKind>,
    next_token: SmolStr,
}

impl<'code> CheckedTinyLexer<'code> {
    pub(crate) fn new(lexer: TinyLexer<'code>, expect: Expect) -> TinyResult<Self> {
        let mut result = Self {
            lexer,
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
        if let Some(next_token) = self.lexer.next() {
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
