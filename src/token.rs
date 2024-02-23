use std::{fmt, num::NonZeroUsize};

use enum_map::Enum;
use paste::paste;
use smallvec::SmallVec;
use smol_str::SmolStr;

use crate::{
    lexer::{CheckedLexer, LexerToken},
    parser::ParseState,
    positioned::{
        lexer::{LexerError, PositionedLexer, PositionedLexerError},
        parser::PositionedTokenStack,
    },
    tiny::{lexer::TinyLexer, parser::TinyTokenStack, TinyError},
};

macro_rules! impl_token_kind {
    (
        $( $Dynamic:ident )*
    'keywords:
        $( $keyword:literal $Keyword:ident )*
    'symbols:
        $( $symbol:literal $Symbol:ident )*
    'chars:
        $( $char:literal $byte_char:literal $Char:ident )*
    ) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Enum)]
        pub(crate) enum TokenKind {
            $( $Dynamic, )*
            $( $Keyword, )*
            $( $Symbol, )*
            $( $Char, )*
        }

        impl TokenKind {
            pub(crate) const fn as_dynamic(self) -> Option<DynamicTokenKind> {
                match self {
                    $( Self::$Dynamic => Some(DynamicTokenKind::$Dynamic), )*
                    _ => None,
                }
            }

            pub(crate) const fn is_dynamic(self) -> bool {
                matches!(self, $( Self::$Dynamic )|* )
            }

            pub(crate) const fn as_fixed(self) -> Option<FixedTokenKind> {
                match self {
                    $( Self::$Keyword => Some(FixedTokenKind::$Keyword), )*
                    $( Self::$Symbol => Some(FixedTokenKind::$Symbol), )*
                    $( Self::$Char => Some(FixedTokenKind::$Char), )*
                    _ => None,
                }
            }
        }

        impl From<DynamicTokenKind> for TokenKind {
            fn from(kind: DynamicTokenKind) -> Self {
                match kind {
                    $( DynamicTokenKind::$Dynamic => Self::$Dynamic, )*
                }
            }
        }

        impl From<FixedTokenKind> for TokenKind {
            fn from(kind: FixedTokenKind) -> Self {
                match kind {
                    $( FixedTokenKind::$Keyword => Self::$Keyword, )*
                    $( FixedTokenKind::$Symbol => Self::$Symbol, )*
                    $( FixedTokenKind::$Char => Self::$Char, )*
                }
            }
        }

        #[derive(Clone, Copy, Debug, PartialEq, Eq, Enum)]
        pub(crate) enum DynamicTokenKind {
            $( $Dynamic, )*
        }

        #[derive(Clone, Copy, Debug, PartialEq, Eq, Enum)]
        pub(crate) enum FixedTokenKind {
            $( $Keyword, )*
            $( $Symbol, )*
            $( $Char, )*
        }

        impl FixedTokenKind {
            const fn text(self) -> &'static str {
                match self {
                    $( Self::$Keyword => $keyword, )*
                    $( Self::$Symbol => $symbol, )*
                    $( Self::$Char => $char, )*
                }
            }

            pub(crate) fn parse_keyword(text: &[u8]) -> Option<Self> { paste! {
                $( const [<$Keyword:upper>]: &[u8] = $keyword.as_bytes(); )*
                match text {
                    $( [<$Keyword:upper>] => Some(Self::$Keyword), )*
                    _ => None,
                }
            } }

            pub(crate) fn parse_symbol(text: &[u8]) -> Option<(Self, usize)> {
                $( if text.starts_with($symbol.as_bytes()) {
                    Some((Self::$Symbol, $symbol.len()))
                } else )+ {
                    None
                }
            }

            pub(crate) fn parse_char(char: u8) -> Option<Self> {
                match char {
                    $( $byte_char => Some(Self::$Char), )*
                    _ => None,
                }
            }
        }

        pub(crate) mod tokens {
            use super::{CheckedLexer, Expect, FixedTokenKind, ParseState, Style, TokenKind, TokenStorage};

            $(
                pub(crate) struct $Dynamic;

                impl<S: Style> TokenStorage<S> for $Dynamic {
                    type Required = S::DynamicRequired;
                    type Optional = S::DynamicOptional;
                    type Repetition = S::DynamicRepetition;
                }

                impl $Dynamic {
                    pub(crate) fn parse_required<S: Style>(
                        lexer: &mut CheckedLexer<S>,
                        expect: Expect,
                    ) -> Result<S::DynamicRequired, S::Error> {
                        S::dynamic_required(lexer, expect)
                    }

                    pub(crate) fn parse_optional<S: Style>(
                        lexer: &mut CheckedLexer<S>,
                        expect: Expect,
                    ) -> Result<S::DynamicOptional, S::Error> {
                        S::dynamic_optional(lexer, TokenKind::$Dynamic, expect)
                    }

                    pub(crate) fn parse_repetition<S: Style>(
                        lexer: &mut CheckedLexer<S>,
                        expect: Expect,
                    ) -> Result<S::DynamicRepetition, S::Error> {
                        S::dynamic_repetition(lexer, TokenKind::$Dynamic, expect)
                    }

                    pub(crate) fn push_required<S: Style>(
                        parser: &mut ParseState<S>,
                        expect: Expect,
                    ) -> Result<(), S::Error> {
                        S::push_dynamic_required(parser, expect)
                    }

                    pub(crate) fn push_optional<S: Style>(
                        parser: &mut ParseState<S>,
                        expect: Expect,
                    ) -> Result<(), S::Error> {
                        S::push_dynamic_optional(parser, TokenKind::$Dynamic, expect)
                    }

                    pub(crate) fn push_repetition<S: Style>(
                        parser: &mut ParseState<S>,
                        expect: Expect,
                    ) -> Result<(), S::Error> {
                        S::push_dynamic_repetition(parser, TokenKind::$Dynamic, expect)
                    }

                    pub(crate) fn pop_required<S: Style>(
                        parser: &mut ParseState<S>,
                    ) -> S::DynamicRequired {
                        S::pop_dynamic_required(parser)
                    }

                    pub(crate) fn pop_optional<S: Style>(
                        parser: &mut ParseState<S>,
                    ) -> S::DynamicOptional {
                        S::pop_dynamic_optional(parser)
                    }

                    pub(crate) fn pop_repetition<S: Style>(
                        parser: &mut ParseState<S>,
                    ) -> S::DynamicRepetition {
                        S::pop_dynamic_repetition(parser)
                    }
                }
            )*

            impl_fixed_token_kind!( $( $Keyword )* $( $Symbol )* $( $Char )* );
        }
    };
}

macro_rules! impl_fixed_token_kind {
    ( $( $Kind:ident )* ) => { $(
        pub(crate) struct $Kind;

        impl $Kind {
            const LEN: usize = FixedTokenKind::$Kind.text().len();
        }

        impl<S: Style> TokenStorage<S> for $Kind {
            type Required = S::FixedRequired<{ Self::LEN }>;
            type Optional = S::FixedOptional<{ Self::LEN }>;
            type Repetition = S::FixedRepetition<{ Self::LEN }>;
        }

        impl $Kind {
            pub(crate) fn parse_required<S: Style>(
                lexer: &mut CheckedLexer<S>,
                expect: Expect,
            ) -> Result<<Self as TokenStorage<S>>::Required, S::Error> {
                S::fixed_required(lexer, expect)
            }

            pub(crate) fn parse_optional<S: Style>(
                lexer: &mut CheckedLexer<S>,
                expect: Expect,
            ) -> Result<<Self as TokenStorage<S>>::Optional, S::Error> {
                S::fixed_optional(lexer, TokenKind::$Kind, expect)
            }

            pub(crate) fn parse_repetition<S: Style>(
                lexer: &mut CheckedLexer<S>,
                expect: Expect,
            ) -> Result<<Self as TokenStorage<S>>::Repetition, S::Error> {
                S::fixed_repetition(lexer, TokenKind::$Kind, expect)
            }

            pub(crate) fn push_required<S: Style>(
                parser: &mut ParseState<S>,
                expect: Expect,
            ) -> Result<(), S::Error> {
                S::push_fixed_required::<{ Self::LEN }>(parser, expect)
            }

            pub(crate) fn push_optional<S: Style>(
                parser: &mut ParseState<S>,
                expect: Expect,
            ) -> Result<(), S::Error> {
                S::push_fixed_optional::<{ Self::LEN }>(parser, TokenKind::$Kind, expect)
            }

            pub(crate) fn push_repetition<S: Style>(
                parser: &mut ParseState<S>,
                expect: Expect,
            ) -> Result<(), S::Error> {
                S::push_fixed_repetition::<{ Self::LEN }>(parser, TokenKind::$Kind, expect)
            }

            pub(crate) fn pop_required<S: Style>(
                parser: &mut ParseState<S>,
            ) -> <Self as TokenStorage<S>>::Required {
                S::pop_fixed_required(parser)
            }

            pub(crate) fn pop_optional<S: Style>(
                parser: &mut ParseState<S>,
            ) -> <Self as TokenStorage<S>>::Optional {
                S::pop_fixed_optional(parser)
            }

            pub(crate) fn pop_repetition<S: Style>(
                parser: &mut ParseState<S>,
            ) -> <Self as TokenStorage<S>>::Repetition {
                S::pop_fixed_repetition(parser)
            }
        }
    )* };
}

pub(crate) trait TokenStorage<S: Style> {
    type Required;
    type Optional;
    type Repetition;
}

impl_token_kind! {
    Ident
    Integer
    Float
    String
    Char
    Label
    DocComment

'keywords:
    "as"       As
    "break"    Break
    "continue" Continue
    "crate"    Crate
    "else"     Else
    "false"    False
    "fn"       Fn
    "for"      For
    "if"       If
    "impl"     Impl
    "in"       In
    "let"      Let
    "loop"     Loop
    "match"    Match
    "mod"      Mod
    "pub"      Pub
    "return"   Return
    "self"     SelfValue
    "Self"     SelfType
    "struct"   Struct
    "super"    Super
    "trait"    Trait
    "true"     True
    "type"     Type
    "_"        Underscore
    "use"      Use
    "while"    While

'symbols:
    "<<=" ShlEq
    ">>=" ShrEq
    "..." DotDotDot
    "..=" DotDotEq

    "&&" AndAnd
    "||" OrOr
    "<<" Shl
    ">>" Shr
    "+=" PlusEq
    "-=" MinusEq
    "*=" StarEq
    "/=" SlashEq
    "%=" PercentEq
    "^=" CaretEq
    "&=" AndEq
    "|=" OrEq
    "==" EqEq
    "!=" Ne
    ">=" Ge
    "<=" Le
    ".." DotDot
    ".=" DotEq
    "::" PathSep
    "->" RArrow
    "=>" FatArrow

'chars:
    "+" b'+' Plus
    "-" b'-' Minus
    "*" b'*' Star
    "/" b'/' Slash
    "%" b'%' Percent
    "^" b'^' Caret
    "!" b'!' Not
    "&" b'&' And
    "|" b'|' Or
    "=" b'=' Eq
    ">" b'>' Gt
    "<" b'<' Lt
    "@" b'@' At
    "." b'.' Dot
    "," b',' Comma
    ";" b';' Semi
    ":" b':' Colon
    "#" b'#' Pound
    "$" b'$' Dollar
    "?" b'?' Question
    "~" b'~' Tilde

    "(" b'(' LParen
    ")" b')' RParen
    "[" b'[' LBrack
    "]" b']' RBrack
    "{" b'{' LCurly
    "}" b'}' RCurly
}

impl FixedTokenKind {
    /// Returns the length of symbols and keywords.
    pub(crate) const fn len(self) -> NonZeroUsize {
        match NonZeroUsize::new(self.text().len()) {
            Some(val) => val,
            None => panic!(),
        }
    }
}

pub(crate) trait Style: Clone + fmt::Debug + PartialEq + Eq {
    type FixedRequired<const N: usize>: Clone + fmt::Debug + PartialEq + Eq;
    type FixedOptional<const N: usize>: Clone + fmt::Debug + PartialEq + Eq;
    type FixedRepetition<const N: usize>: Clone + fmt::Debug + PartialEq + Eq;

    type DynamicRequired: Clone + fmt::Debug + PartialEq + Eq;
    type DynamicOptional: Clone + fmt::Debug + PartialEq + Eq;
    type DynamicRepetition: Clone + fmt::Debug + PartialEq + Eq;

    type Lexer<'code>: fmt::Debug + Iterator<Item = Result<LexerToken<Self>, Self::Error>>;
    type Token: fmt::Debug;
    type Pos: fmt::Debug + Copy + Default;
    type TokenStack: fmt::Debug + Default;
    type Error: fmt::Debug;

    const ARBITRARY_TOKEN: Self::Token;

    fn new_lexer(code: &str) -> Result<Self::Lexer<'_>, Self::Error>;
    fn lexer_pos(lexer: &Self::Lexer<'_>) -> Self::Pos;

    fn finish_token_stack(stack: Self::TokenStack) -> bool;

    fn unexpected_token(
        lexer: &Self::Lexer<'_>,
        expect: Expect,
        found: Option<TokenKind>,
    ) -> Self::Error;

    fn fixed_required<const N: usize>(
        lexer: &mut CheckedLexer<Self>,
        expect: Expect,
    ) -> Result<Self::FixedRequired<N>, Self::Error>;
    fn fixed_optional<const N: usize>(
        lexer: &mut CheckedLexer<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedOptional<N>, Self::Error>;
    fn fixed_repetition<const N: usize>(
        lexer: &mut CheckedLexer<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedRepetition<N>, Self::Error>;

    fn push_fixed_required<const N: usize>(
        state: &mut ParseState<Self>,
        expect: Expect,
    ) -> Result<(), Self::Error>;
    fn push_fixed_optional<const N: usize>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), Self::Error>;
    fn push_fixed_repetition<const N: usize>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), Self::Error>;

    fn pop_fixed_required<const N: usize>(state: &mut ParseState<Self>) -> Self::FixedRequired<N>;
    fn pop_fixed_optional<const N: usize>(state: &mut ParseState<Self>) -> Self::FixedOptional<N>;
    fn pop_fixed_repetition<const N: usize>(
        state: &mut ParseState<Self>,
    ) -> Self::FixedRepetition<N>;

    fn dynamic_required(
        lexer: &mut CheckedLexer<Self>,
        expect: Expect,
    ) -> Result<Self::DynamicRequired, Self::Error>;
    fn dynamic_optional(
        lexer: &mut CheckedLexer<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::DynamicOptional, Self::Error>;
    fn dynamic_repetition(
        lexer: &mut CheckedLexer<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::DynamicRepetition, Self::Error>;

    fn push_dynamic_required(
        state: &mut ParseState<Self>,
        expect: Expect,
    ) -> Result<(), Self::Error>;
    fn push_dynamic_optional(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), Self::Error>;
    fn push_dynamic_repetition(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), Self::Error>;

    fn pop_dynamic_required(state: &mut ParseState<Self>) -> Self::DynamicRequired;
    fn pop_dynamic_optional(state: &mut ParseState<Self>) -> Self::DynamicOptional;
    fn pop_dynamic_repetition(state: &mut ParseState<Self>) -> Self::DynamicRepetition;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Tiny;

impl Style for Tiny {
    type FixedRequired<const N: usize> = ();
    type FixedOptional<const N: usize> = bool;
    type FixedRepetition<const N: usize> = usize;

    type DynamicRequired = SmolStr;
    type DynamicOptional = Option<SmolStr>;
    type DynamicRepetition = SmallVec<[SmolStr; 1]>;

    type Lexer<'code> = TinyLexer<'code>;
    type Token = SmolStr;
    type Pos = ();
    type TokenStack = TinyTokenStack;
    type Error = TinyError;

    const ARBITRARY_TOKEN: Self::Token = SmolStr::new_inline("");

    fn new_lexer(code: &str) -> Result<Self::Lexer<'_>, Self::Error> {
        TinyLexer::new(code)
    }

    fn lexer_pos(_lexer: &Self::Lexer<'_>) -> Self::Pos {}

    fn finish_token_stack(stack: Self::TokenStack) -> bool {
        stack.finish()
    }

    fn unexpected_token(
        _lexer: &Self::Lexer<'_>,
        _expect: Expect,
        _found: Option<TokenKind>,
    ) -> Self::Error {
        TinyError
    }

    fn fixed_required<const N: usize>(
        lexer: &mut CheckedLexer<Self>,
        expect: Expect,
    ) -> Result<Self::FixedRequired<N>, Self::Error> {
        lexer.next(expect)?;
        Ok(())
    }

    fn fixed_optional<const N: usize>(
        lexer: &mut CheckedLexer<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedOptional<N>, Self::Error> {
        let matches = lexer.matches(kind);
        if matches {
            lexer.next(expect)?;
        }
        Ok(matches)
    }

    fn fixed_repetition<const N: usize>(
        lexer: &mut CheckedLexer<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedRepetition<N>, Self::Error> {
        let mut count = 0;
        while lexer.matches(kind) {
            count += 1;
            lexer.next(expect)?;
        }
        Ok(count)
    }

    fn push_fixed_required<const N: usize>(
        state: &mut ParseState<Self>,
        expect: Expect,
    ) -> Result<(), Self::Error> {
        state.lexer.next(expect)?;
        Ok(())
    }

    fn push_fixed_optional<const N: usize>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), Self::Error> {
        if state.lexer.matches(kind) {
            state.lexer.next(expect)?;
            state.tokens.push_fixed_some();
        } else {
            state.tokens.push_none();
        }
        Ok(())
    }

    fn push_fixed_repetition<const N: usize>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), Self::Error> {
        let mut count = 0;
        while state.lexer.matches(kind) {
            count += 1;
            state.lexer.next(expect)?;
        }
        state.tokens.push_fixed_repetition(count);
        Ok(())
    }

    fn pop_fixed_required<const N: usize>(_state: &mut ParseState<Self>) -> Self::FixedRequired<N> {
        // nothing to pop
    }

    fn pop_fixed_optional<const N: usize>(state: &mut ParseState<Self>) -> Self::FixedOptional<N> {
        state.tokens.pop_fixed_optional()
    }

    fn pop_fixed_repetition<const N: usize>(
        state: &mut ParseState<Self>,
    ) -> Self::FixedRepetition<N> {
        state.tokens.pop_fixed_repetition()
    }

    fn dynamic_required(
        lexer: &mut CheckedLexer<Self>,
        expect: Expect,
    ) -> Result<Self::DynamicRequired, Self::Error> {
        lexer.next(expect)
    }

    fn dynamic_optional(
        lexer: &mut CheckedLexer<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::DynamicOptional, Self::Error> {
        if lexer.matches(kind) {
            lexer.next(expect).map(Some)
        } else {
            Ok(None)
        }
    }

    fn dynamic_repetition(
        lexer: &mut CheckedLexer<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::DynamicRepetition, Self::Error> {
        let mut result = SmallVec::new();
        while lexer.matches(kind) {
            result.push(lexer.next(expect)?);
        }
        Ok(result)
    }

    fn push_dynamic_required(
        state: &mut ParseState<Self>,
        expect: Expect,
    ) -> Result<(), Self::Error> {
        state.tokens.push_dynamic(state.lexer.next(expect)?);
        Ok(())
    }

    fn push_dynamic_optional(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), Self::Error> {
        if state.lexer.matches(kind) {
            state.tokens.push_dynamic_some(state.lexer.next(expect)?);
        } else {
            state.tokens.push_none();
        }
        Ok(())
    }

    fn push_dynamic_repetition(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), Self::Error> {
        state.tokens.start_dynamic_repetition();
        while state.lexer.matches(kind) {
            Self::push_dynamic_required(state, expect)?;
        }
        Ok(())
    }

    fn pop_dynamic_required(state: &mut ParseState<Self>) -> Self::DynamicRequired {
        state.tokens.pop_dynamic()
    }

    fn pop_dynamic_optional(state: &mut ParseState<Self>) -> Self::DynamicOptional {
        state.tokens.pop_dynamic_optional()
    }

    fn pop_dynamic_repetition(state: &mut ParseState<Self>) -> Self::DynamicRepetition {
        state.tokens.pop_dynamic_repetition().collect()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Positioned;

impl Style for Positioned {
    type FixedRequired<const N: usize> = FixedTokenSpan<N>;
    type FixedOptional<const N: usize> = FixedOptionalTokenSpan<N>;
    type FixedRepetition<const N: usize> = FixedRepetitionTokenSpan<N>;

    type DynamicRequired = TokenSpan;
    type DynamicOptional = OptionalTokenSpan;
    type DynamicRepetition = RepetitionTokenSpan;

    type Lexer<'code> = PositionedLexer<'code>;
    type Token = NonZeroUsize;
    type Pos = usize;
    type TokenStack = PositionedTokenStack;
    type Error = PositionedLexerError;

    const ARBITRARY_TOKEN: Self::Token = NonZeroUsize::MIN;

    fn new_lexer(code: &str) -> Result<Self::Lexer<'_>, Self::Error> {
        PositionedLexer::new(code)
    }

    fn lexer_pos(lexer: &Self::Lexer<'_>) -> Self::Pos {
        lexer.pos()
    }

    fn finish_token_stack(stack: Self::TokenStack) -> bool {
        stack.finish()
    }

    fn unexpected_token(
        lexer: &Self::Lexer<'_>,
        expect: Expect,
        found: Option<TokenKind>,
    ) -> Self::Error {
        PositionedLexerError {
            pos: lexer.pos(),
            kind: LexerError::UnexpectedToken { expect, found },
        }
    }

    fn fixed_required<const N: usize>(
        lexer: &mut CheckedLexer<Self>,
        expect: Expect,
    ) -> Result<Self::FixedRequired<N>, Self::Error> {
        lexer.next(expect)?;
        Ok(FixedTokenSpan { pos: lexer.pos() })
    }

    fn fixed_optional<const N: usize>(
        lexer: &mut CheckedLexer<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedOptional<N>, Self::Error> {
        let pos = lexer.pos();
        let some = lexer.matches(kind);
        if some {
            lexer.next(expect)?;
        }
        Ok(FixedOptionalTokenSpan { pos, some })
    }

    fn fixed_repetition<const N: usize>(
        lexer: &mut CheckedLexer<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedRepetition<N>, Self::Error> {
        let pos = lexer.pos();
        let mut tokens = SmallVec::new();
        while lexer.matches(kind) {
            tokens.push(Self::fixed_required(lexer, expect)?);
        }
        Ok(FixedRepetitionTokenSpan { pos, tokens })
    }

    fn push_fixed_required<const N: usize>(
        state: &mut ParseState<Self>,
        expect: Expect,
    ) -> Result<(), Self::Error> {
        state
            .tokens
            .push_fixed(Self::fixed_required::<N>(&mut state.lexer, expect)?);
        Ok(())
    }

    fn push_fixed_optional<const N: usize>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), Self::Error> {
        state.tokens.push_fixed_optional(Self::fixed_optional::<N>(
            &mut state.lexer,
            kind,
            expect,
        )?);
        Ok(())
    }

    fn push_fixed_repetition<const N: usize>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), Self::Error> {
        state
            .tokens
            .push_fixed_repetition(Self::fixed_repetition::<N>(&mut state.lexer, kind, expect)?);
        Ok(())
    }

    fn pop_fixed_required<const N: usize>(state: &mut ParseState<Self>) -> Self::FixedRequired<N> {
        state.tokens.pop_fixed()
    }

    fn pop_fixed_optional<const N: usize>(state: &mut ParseState<Self>) -> Self::FixedOptional<N> {
        state.tokens.pop_fixed_optional()
    }

    fn pop_fixed_repetition<const N: usize>(
        state: &mut ParseState<Self>,
    ) -> Self::FixedRepetition<N> {
        state.tokens.pop_fixed_repetition()
    }

    fn dynamic_required(
        lexer: &mut CheckedLexer<Self>,
        expect: Expect,
    ) -> Result<Self::DynamicRequired, Self::Error> {
        Ok(TokenSpan {
            pos: lexer.pos(),
            len: lexer.next(expect)?,
        })
    }

    fn dynamic_optional(
        lexer: &mut CheckedLexer<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::DynamicOptional, Self::Error> {
        Ok(OptionalTokenSpan {
            pos: lexer.pos(),
            len: if lexer.matches(kind) {
                Some(Self::dynamic_required(lexer, expect)?.len)
            } else {
                None
            },
        })
    }

    fn dynamic_repetition(
        lexer: &mut CheckedLexer<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::DynamicRepetition, Self::Error> {
        let mut tokens = SmallVec::new();
        while lexer.matches(kind) {
            tokens.push(Self::dynamic_required(lexer, expect)?);
        }
        Ok(RepetitionTokenSpan {
            pos: lexer.pos(),
            tokens,
        })
    }

    fn push_dynamic_required(
        state: &mut ParseState<Self>,
        expect: Expect,
    ) -> Result<(), Self::Error> {
        state
            .tokens
            .push_dynamic(Self::dynamic_required(&mut state.lexer, expect)?);
        Ok(())
    }

    fn push_dynamic_optional(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), Self::Error> {
        state
            .tokens
            .push_dynamic_optional(Self::dynamic_optional(&mut state.lexer, kind, expect)?);
        Ok(())
    }

    fn push_dynamic_repetition(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), Self::Error> {
        state
            .tokens
            .push_dynamic_repetition(Self::dynamic_repetition(&mut state.lexer, kind, expect)?);
        Ok(())
    }

    fn pop_dynamic_required(state: &mut ParseState<Self>) -> Self::DynamicRequired {
        state.tokens.pop_dynamic()
    }

    fn pop_dynamic_optional(state: &mut ParseState<Self>) -> Self::DynamicOptional {
        state.tokens.pop_dynamic_optional()
    }

    fn pop_dynamic_repetition(state: &mut ParseState<Self>) -> Self::DynamicRepetition {
        state.tokens.pop_dynamic_repetition()
    }
}

#[derive(Clone, Copy, Default, Hash, PartialEq, Eq)]
pub(crate) struct TokenSet(pub(crate) u128);

impl fmt::Debug for TokenSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.tokens()).finish()
    }
}

impl TokenSet {
    pub(crate) const fn new() -> Self {
        Self(0)
    }

    pub(crate) const fn is_empty(self) -> bool {
        self.0 == 0
    }

    pub(crate) const fn from_kind(kind: TokenKind) -> Self {
        Self(1 << kind as u8)
    }

    pub(crate) const fn xor_without_ambiguity_const(self, other: Self) -> Self {
        let merged = self.0 ^ other.0;
        if merged != self.0 | other.0 {
            panic!("ambiguous token set");
        }
        Self(merged)
    }

    pub(crate) fn xor_without_ambiguity(self, other: Self) -> Self {
        let overlap = self.0 & other.0;
        if overlap != 0 {
            panic!("ambiguous token set because of {:?}", Self(overlap));
        }
        Self(self.0 | other.0)
    }

    pub(crate) const fn contains(self, kind: TokenKind) -> bool {
        self.0 & (1 << kind as u8) != 0
    }

    pub(crate) fn tokens(self) -> impl Iterator<Item = TokenKind> {
        (0..TokenKind::LENGTH)
            .map(TokenKind::from_usize)
            .filter(move |&kind| self.contains(kind))
    }
}

impl From<TokenKind> for TokenSet {
    fn from(kind: TokenKind) -> Self {
        Self::from_kind(kind)
    }
}

/// A full set of what to expected as the next token.
///
/// In addition to expecting any kind of node, it can also expect the end of the input.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct Expect {
    pub(crate) tokens: TokenSet,
    pub(crate) or_end_of_input: bool,
}

impl fmt::Debug for Expect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut list = f.debug_list();
        list.entries(self.tokens.tokens());
        if self.or_end_of_input {
            list.entry(&"END_OF_INPUT");
        }
        list.finish()
    }
}

impl Expect {
    /// Expects only the end of the input and no actual tokens.
    pub(crate) const END_OF_INPUT: Self = Self {
        tokens: TokenSet::new(),
        or_end_of_input: true,
    };
}

/// A set of tokens, as a flag for whether this set is exhaustive.
///
/// If a set is *not* exhaustive, the caller has to xor it with whatever he expects next.
///
/// Exhaustiveness is used by trailing optional and repetition fields on structs. Since those can
/// match "nothing" and the struct itself does not know what would come next, it has to be passed in
/// from the caller instead.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct NestedTokenSet {
    pub(crate) tokens: TokenSet,
    pub(crate) exhaustive: bool,
}

impl NestedTokenSet {
    pub(crate) const fn new() -> Self {
        Self {
            tokens: TokenSet::new(),
            exhaustive: true,
        }
    }

    pub(crate) const fn from_kind(kind: TokenKind) -> Self {
        Self {
            tokens: TokenSet::from_kind(kind),
            exhaustive: true,
        }
    }

    pub(crate) const fn xor_without_ambiguity_const(self, other: Self) -> Self {
        Self {
            tokens: self.tokens.xor_without_ambiguity_const(other.tokens),
            exhaustive: self.exhaustive || other.exhaustive,
        }
    }

    pub(crate) fn xor_without_ambiguity(self, other: Self) -> Self {
        Self {
            tokens: self.tokens.xor_without_ambiguity(other.tokens),
            exhaustive: self.exhaustive || other.exhaustive,
        }
    }

    pub(crate) const fn non_exhaustive(self) -> Self {
        Self {
            exhaustive: false,
            ..self
        }
    }

    pub(crate) fn expect(self, expect: Expect) -> Expect {
        if self.exhaustive {
            Expect {
                tokens: self.tokens,
                or_end_of_input: false,
            }
        } else {
            Expect {
                tokens: expect.tokens.xor_without_ambiguity(self.tokens),
                or_end_of_input: expect.or_end_of_input,
            }
        }
    }
}

impl From<TokenKind> for NestedTokenSet {
    fn from(kind: TokenKind) -> Self {
        Self::from_kind(kind)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TokenSpan {
    pub(crate) pos: usize,
    pub(crate) len: NonZeroUsize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct OptionalTokenSpan {
    pub(crate) pos: usize,
    pub(crate) len: Option<NonZeroUsize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RepetitionTokenSpan {
    pub(crate) pos: usize,
    pub(crate) tokens: SmallVec<[TokenSpan; 1]>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FixedTokenSpan<const N: usize> {
    pub(crate) pos: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FixedOptionalTokenSpan<const N: usize> {
    pub(crate) pos: usize,
    pub(crate) some: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FixedRepetitionTokenSpan<const N: usize> {
    pub(crate) pos: usize,
    pub(crate) tokens: SmallVec<[FixedTokenSpan<N>; 1]>,
}
