use std::{fmt, num::NonZeroUsize, ops::Range};

use bitvec::vec::BitVec;
use enum_map::Enum;
use paste::paste;
use smallvec::SmallVec;

use crate::{
    lexer::{CheckedLexer, LexerError},
    parser::ParseState,
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
            use super::{
                CheckedLexer, Expect, FixedTokenKind, LexerError, OptionalTokenSpan, ParseState,
                SmallVec, Style, TokenKind, TokenSpan, TokenSpanRepetition, TokenStorage,
            };

            $(
                pub(crate) struct $Dynamic;

                impl<S: Style> TokenStorage<S> for $Dynamic {
                    type Required = TokenSpan;
                    type Optional = OptionalTokenSpan;
                    type Repetition = TokenSpanRepetition;
                }

                impl $Dynamic {
                    pub(crate) fn parse_required<S: Style>(
                        lexer: &mut CheckedLexer,
                        expect: Expect,
                    ) -> Result<TokenSpan, LexerError> {
                        Ok(TokenSpan {
                            pos: lexer.pos(),
                            len: lexer.next(expect)?,
                        })
                    }

                    pub(crate) fn push_required<S: Style>(
                        parser: &mut ParseState<S>,
                        expect: Expect,
                    ) -> Result<(), LexerError> {
                        parser.tokens.push_dynamic(Self::parse_required::<S>(&mut parser.lexer, expect)?);
                        Ok(())
                    }

                    pub(crate) fn pop_required<S: Style>(
                        parser: &mut ParseState<S>,
                    ) -> TokenSpan {
                        parser.tokens.pop_dynamic()
                    }

                    pub(crate) fn parse_optional<S: Style>(
                        lexer: &mut CheckedLexer,
                        expect: Expect,
                    ) -> Result<OptionalTokenSpan, LexerError> {
                        Ok(OptionalTokenSpan {
                            pos: lexer.pos(),
                            len: if lexer.matches(TokenKind::$Dynamic) { Some(lexer.next(expect)?) } else { None },
                        })
                    }

                    pub(crate) fn push_optional<S: Style>(
                        parser: &mut ParseState<S>,
                        expect: Expect,
                    ) -> Result<(), LexerError> {
                        parser.tokens.push_dynamic_optional(Self::parse_optional::<S>(&mut parser.lexer, expect)?);
                        Ok(())
                    }

                    pub(crate) fn pop_optional<S: Style>(
                        parser: &mut ParseState<S>,
                    ) -> OptionalTokenSpan {
                        parser.tokens.pop_dynamic_optional()
                    }

                    pub(crate) fn parse_repetition<S: Style>(
                        lexer: &mut CheckedLexer,
                        expect: Expect,
                    ) -> Result<TokenSpanRepetition, LexerError> {
                        Ok(TokenSpanRepetition {
                            pos: lexer.pos(),
                            tokens: {
                                let mut tokens = SmallVec::new();
                                while lexer.matches(TokenKind::$Dynamic) {
                                    tokens.push(TokenSpan {
                                        pos: lexer.pos(),
                                        len: lexer.next(expect)?,
                                    });
                                }
                                tokens
                            },
                        })
                    }

                    pub(crate) fn push_repetition<S: Style>(
                        parser: &mut ParseState<S>,
                        expect: Expect,
                    ) -> Result<(), LexerError> {
                        parser.tokens.push_dynamic_repetition(Self::parse_repetition::<S>(&mut parser.lexer, expect)?);
                        Ok(())
                    }

                    pub(crate) fn pop_repetition<S: Style>(
                        parser: &mut ParseState<S>,
                    ) -> TokenSpanRepetition {
                        parser.tokens.pop_dynamic_repetition()
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
                lexer: &mut CheckedLexer,
                expect: Expect,
            ) -> Result<<Self as TokenStorage<S>>::Required, LexerError> {
                S::fixed_required(lexer, expect)
            }

            pub(crate) fn push_required<S: Style>(
                parser: &mut ParseState<S>,
                expect: Expect,
            ) -> Result<(), LexerError> {
                S::push_fixed_required::<{ Self::LEN }>(parser, expect)
            }

            pub(crate) fn pop_required<S: Style>(
                parser: &mut ParseState<S>,
            ) -> <Self as TokenStorage<S>>::Required {
                S::pop_fixed_required(parser)
            }

            pub(crate) fn parse_optional<S: Style>(
                lexer: &mut CheckedLexer,
                expect: Expect,
            ) -> Result<<Self as TokenStorage<S>>::Optional, LexerError> {
                S::fixed_optional(lexer, TokenKind::$Kind, expect)
            }

            pub(crate) fn push_optional<S: Style>(
                parser: &mut ParseState<S>,
                expect: Expect,
            ) -> Result<(), LexerError> {
                S::push_fixed_optional::<{ Self::LEN }>(parser, TokenKind::$Kind, expect)
            }

            pub(crate) fn pop_optional<S: Style>(
                parser: &mut ParseState<S>,
            ) -> <Self as TokenStorage<S>>::Optional {
                S::pop_fixed_optional(parser)
            }

            pub(crate) fn parse_repetition<S: Style>(
                lexer: &mut CheckedLexer,
                expect: Expect,
            ) -> Result<<Self as TokenStorage<S>>::Repetition, LexerError> {
                S::fixed_repetition(lexer, TokenKind::$Kind, expect)
            }

            pub(crate) fn push_repetition<S: Style>(
                parser: &mut ParseState<S>,
                expect: Expect,
            ) -> Result<(), LexerError> {
                S::push_fixed_repetition::<{ Self::LEN }>(parser, TokenKind::$Kind, expect)
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
    type FixedRequired<const N: usize>: Clone + Copy + fmt::Debug + PartialEq + Eq + TryCodeSpan;
    type FixedOptional<const N: usize>: Clone + Copy + fmt::Debug + PartialEq + Eq + TryCodeSpan;
    type FixedRepetition<const N: usize>: Clone + fmt::Debug + PartialEq + Eq + TryCodeSpan;

    fn fixed_required<const N: usize>(
        lexer: &mut CheckedLexer,
        expect: Expect,
    ) -> Result<Self::FixedRequired<N>, LexerError>;

    fn push_fixed_required<const N: usize>(
        state: &mut ParseState<Self>,
        expect: Expect,
    ) -> Result<(), LexerError>;

    fn pop_fixed_required<const N: usize>(state: &mut ParseState<Self>) -> Self::FixedRequired<N>;

    fn fixed_optional<const N: usize>(
        lexer: &mut CheckedLexer,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedOptional<N>, LexerError>;

    fn push_fixed_optional<const N: usize>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), LexerError>;

    fn pop_fixed_optional<const N: usize>(state: &mut ParseState<Self>) -> Self::FixedOptional<N>;

    fn fixed_repetition<const N: usize>(
        lexer: &mut CheckedLexer,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedRepetition<N>, LexerError>;

    fn push_fixed_repetition<const N: usize>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), LexerError>;

    fn pop_fixed_repetition<const N: usize>(
        state: &mut ParseState<Self>,
    ) -> Self::FixedRepetition<N>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Tiny;

impl Style for Tiny {
    type FixedRequired<const N: usize> = TinyToken;
    type FixedOptional<const N: usize> = TinyOptionalToken;
    type FixedRepetition<const N: usize> = TinyTokenRepetition;

    fn fixed_required<const N: usize>(
        lexer: &mut CheckedLexer,
        expect: Expect,
    ) -> Result<Self::FixedRequired<N>, LexerError> {
        lexer.next(expect)?;
        Ok(TinyToken)
    }

    fn push_fixed_required<const N: usize>(
        state: &mut ParseState<Self>,
        expect: Expect,
    ) -> Result<(), LexerError> {
        state.lexer.next(expect)?;
        // pushing nothing
        Ok(())
    }

    fn pop_fixed_required<const N: usize>(_state: &mut ParseState<Self>) -> Self::FixedRequired<N> {
        // pop nothing
        TinyToken
    }

    fn fixed_optional<const N: usize>(
        lexer: &mut CheckedLexer,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedOptional<N>, LexerError> {
        let some = lexer.matches(kind);
        if some {
            lexer.next(expect)?;
        }
        Ok(TinyOptionalToken { some })
    }

    fn push_fixed_optional<const N: usize>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), LexerError> {
        if state.lexer.matches(kind) {
            state.lexer.next(expect)?;
            state.tokens.push_tiny_fixed_optional(true);
        } else {
            state.tokens.push_tiny_fixed_optional(false);
        }
        Ok(())
    }

    fn pop_fixed_optional<const N: usize>(state: &mut ParseState<Self>) -> Self::FixedOptional<N> {
        TinyOptionalToken {
            some: state.tokens.pop_tiny_fixed_optional(),
        }
    }

    fn fixed_repetition<const N: usize>(
        lexer: &mut CheckedLexer,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedRepetition<N>, LexerError> {
        let mut count = 0;
        while lexer.matches(kind) {
            count += 1;
            lexer.next(expect)?;
        }
        Ok(TinyTokenRepetition { count })
    }

    fn push_fixed_repetition<const N: usize>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), LexerError> {
        let mut count = 0;
        while state.lexer.matches(kind) {
            count += 1;
            state.lexer.next(expect)?;
        }
        state.tokens.push_tiny_fixed_repetition(count);
        Ok(())
    }

    fn pop_fixed_repetition<const N: usize>(
        state: &mut ParseState<Self>,
    ) -> Self::FixedRepetition<N> {
        TinyTokenRepetition {
            count: state.tokens.pop_tiny_fixed_repetition(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Full;

impl Style for Full {
    type FixedRequired<const N: usize> = FixedTokenSpan<N>;
    type FixedOptional<const N: usize> = FixedOptionalTokenSpan<N>;
    type FixedRepetition<const N: usize> = FixedTokenSpanRepetition<N>;

    fn fixed_required<const N: usize>(
        lexer: &mut CheckedLexer,
        expect: Expect,
    ) -> Result<Self::FixedRequired<N>, LexerError> {
        let pos = lexer.pos();
        lexer.next(expect)?;
        Ok(FixedTokenSpan { pos })
    }

    fn push_fixed_required<const N: usize>(
        state: &mut ParseState<Self>,
        expect: Expect,
    ) -> Result<(), LexerError> {
        state
            .tokens
            .push_fixed(Self::fixed_required::<N>(&mut state.lexer, expect)?);
        Ok(())
    }

    fn pop_fixed_required<const N: usize>(state: &mut ParseState<Self>) -> Self::FixedRequired<N> {
        state.tokens.pop_fixed()
    }

    fn fixed_optional<const N: usize>(
        lexer: &mut CheckedLexer,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedOptional<N>, LexerError> {
        let pos = lexer.pos();
        let some = lexer.matches(kind);
        if some {
            lexer.next(expect)?;
        }
        Ok(FixedOptionalTokenSpan { pos, some })
    }

    fn push_fixed_optional<const N: usize>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), LexerError> {
        state.tokens.push_fixed_optional(Self::fixed_optional::<N>(
            &mut state.lexer,
            kind,
            expect,
        )?);
        Ok(())
    }

    fn pop_fixed_optional<const N: usize>(state: &mut ParseState<Self>) -> Self::FixedOptional<N> {
        state.tokens.pop_fixed_optional()
    }

    fn fixed_repetition<const N: usize>(
        lexer: &mut CheckedLexer,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedRepetition<N>, LexerError> {
        let pos = lexer.pos();
        let mut tokens = SmallVec::new();
        while lexer.matches(kind) {
            tokens.push(Self::fixed_required(lexer, expect)?);
        }
        Ok(FixedTokenSpanRepetition { pos, tokens })
    }

    fn push_fixed_repetition<const N: usize>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), LexerError> {
        state
            .tokens
            .push_fixed_repetition(Self::fixed_repetition::<N>(&mut state.lexer, kind, expect)?);
        Ok(())
    }

    fn pop_fixed_repetition<const N: usize>(
        state: &mut ParseState<Self>,
    ) -> Self::FixedRepetition<N> {
        state.tokens.pop_fixed_repetition()
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

pub(crate) trait TryCodeSpan {
    fn try_code_span(&self) -> Option<Range<usize>>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TokenSpan {
    pub(crate) pos: usize,
    pub(crate) len: NonZeroUsize,
}

impl TokenSpan {
    pub(crate) fn code_span(self) -> Range<usize> {
        Range {
            start: self.pos,
            end: self.pos + self.len.get(),
        }
    }
}

impl TryCodeSpan for TokenSpan {
    fn try_code_span(&self) -> Option<Range<usize>> {
        Some(self.code_span())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct OptionalTokenSpan {
    pub(crate) pos: usize,
    pub(crate) len: Option<NonZeroUsize>,
}

impl OptionalTokenSpan {
    pub(crate) fn code_span(self) -> Range<usize> {
        Range {
            start: self.pos,
            end: self.pos + self.len.map_or(0, |len| len.get()),
        }
    }
}

impl TryCodeSpan for OptionalTokenSpan {
    fn try_code_span(&self) -> Option<Range<usize>> {
        Some(self.code_span())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TokenSpanRepetition {
    pub(crate) pos: usize,
    pub(crate) tokens: SmallVec<[TokenSpan; 1]>,
}

impl TokenSpanRepetition {
    fn code_span(&self) -> Range<usize> {
        Range {
            start: self.pos,
            end: self.pos
                + self
                    .tokens
                    .last()
                    .map_or(0, |token| token.pos - self.pos + token.len.get()),
        }
    }
}

impl TryCodeSpan for TokenSpanRepetition {
    fn try_code_span(&self) -> Option<Range<usize>> {
        Some(self.code_span())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FixedTokenSpan<const N: usize> {
    pub(crate) pos: usize,
}

impl<const N: usize> FixedTokenSpan<N> {
    fn code_span(self) -> Range<usize> {
        Range {
            start: self.pos,
            end: self.pos + N,
        }
    }
}

impl<const N: usize> TryCodeSpan for FixedTokenSpan<N> {
    fn try_code_span(&self) -> Option<Range<usize>> {
        Some(self.code_span())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FixedOptionalTokenSpan<const N: usize> {
    pub(crate) pos: usize,
    pub(crate) some: bool,
}

impl<const N: usize> FixedOptionalTokenSpan<N> {
    fn code_span(self) -> Range<usize> {
        Range {
            start: self.pos,
            end: self.pos + if self.some { N } else { 0 },
        }
    }
}

impl<const N: usize> TryCodeSpan for FixedOptionalTokenSpan<N> {
    fn try_code_span(&self) -> Option<Range<usize>> {
        Some(self.code_span())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FixedTokenSpanRepetition<const N: usize> {
    pub(crate) pos: usize,
    pub(crate) tokens: SmallVec<[FixedTokenSpan<N>; 1]>,
}

impl<const N: usize> FixedTokenSpanRepetition<N> {
    fn code_span(&self) -> Range<usize> {
        Range {
            start: self.pos,
            end: self.pos
                + self
                    .tokens
                    .last()
                    .map_or(0, |token| token.pos - self.pos + N),
        }
    }
}

impl<const N: usize> TryCodeSpan for FixedTokenSpanRepetition<N> {
    fn try_code_span(&self) -> Option<Range<usize>> {
        Some(self.code_span())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TinyToken;

impl TryCodeSpan for TinyToken {
    fn try_code_span(&self) -> Option<Range<usize>> {
        None
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TinyOptionalToken {
    pub(crate) some: bool,
}

impl TryCodeSpan for TinyOptionalToken {
    fn try_code_span(&self) -> Option<Range<usize>> {
        None
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TinyTokenRepetition {
    pub(crate) count: usize,
}

impl TryCodeSpan for TinyTokenRepetition {
    fn try_code_span(&self) -> Option<Range<usize>> {
        None
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct TokenStack {
    data: Vec<usize>,
    optionals: BitVec,
}

impl TokenStack {
    pub(crate) fn finish(self) -> bool {
        self.data.is_empty() && self.optionals.is_empty()
    }

    pub(crate) fn push_fixed<const N: usize>(&mut self, token: FixedTokenSpan<N>) {
        self.data.push(token.pos);
    }

    pub(crate) fn pop_fixed<const N: usize>(&mut self) -> FixedTokenSpan<N> {
        FixedTokenSpan { pos: self.pop() }
    }

    pub(crate) fn push_fixed_optional<const N: usize>(&mut self, token: FixedOptionalTokenSpan<N>) {
        self.optionals.push(token.some);
        self.data.push(token.pos);
    }

    pub(crate) fn pop_fixed_optional<const N: usize>(&mut self) -> FixedOptionalTokenSpan<N> {
        FixedOptionalTokenSpan {
            pos: self.pop(),
            some: self.pop_optional(),
        }
    }

    pub(crate) fn push_tiny_fixed_optional(&mut self, some: bool) {
        self.optionals.push(some);
    }

    pub(crate) fn pop_tiny_fixed_optional(&mut self) -> bool {
        self.pop_optional()
    }

    pub(crate) fn push_fixed_repetition<const N: usize>(
        &mut self,
        repetition: FixedTokenSpanRepetition<N>,
    ) {
        self.data
            .extend(repetition.tokens.iter().rev().map(|token| token.pos));
        self.data.push(repetition.tokens.len());
        self.data.push(repetition.pos);
    }

    pub(crate) fn pop_fixed_repetition<const N: usize>(&mut self) -> FixedTokenSpanRepetition<N> {
        FixedTokenSpanRepetition {
            pos: self.pop(),
            tokens: {
                (0..self.pop())
                    .map(|_| FixedTokenSpan { pos: self.pop() })
                    .collect()
            },
        }
    }

    pub(crate) fn push_tiny_fixed_repetition(&mut self, count: usize) {
        self.data.push(count);
    }

    pub(crate) fn pop_tiny_fixed_repetition(&mut self) -> usize {
        self.pop()
    }

    pub(crate) fn push_dynamic(&mut self, token: TokenSpan) {
        self.data.push(token.len.get());
        self.data.push(token.pos);
    }

    pub(crate) fn pop_dynamic(&mut self) -> TokenSpan {
        TokenSpan {
            pos: self.pop(),
            len: self.pop_len(),
        }
    }

    pub(crate) fn push_dynamic_optional(&mut self, token: OptionalTokenSpan) {
        if let Some(len) = token.len {
            self.data.push(len.get());
        }
        self.optionals.push(token.len.is_some());
        self.data.push(token.pos);
    }

    pub(crate) fn pop_dynamic_optional(&mut self) -> OptionalTokenSpan {
        OptionalTokenSpan {
            pos: self.data.pop().expect("data stack should not be empty"),
            len: self.pop_optional().then(|| self.pop_len()),
        }
    }

    pub(crate) fn push_dynamic_repetition(&mut self, repetition: TokenSpanRepetition) {
        self.data.extend(
            repetition
                .tokens
                .iter()
                .rev()
                .flat_map(|token| [token.len.get(), token.pos]),
        );
        self.data.push(repetition.tokens.len());
        self.data.push(repetition.pos);
    }

    pub(crate) fn pop_dynamic_repetition(&mut self) -> TokenSpanRepetition {
        TokenSpanRepetition {
            pos: self.pop(),
            tokens: {
                (0..self.pop())
                    .map(|_| TokenSpan {
                        pos: self.pop(),
                        len: self.pop_len(),
                    })
                    .collect()
            },
        }
    }

    fn pop(&mut self) -> usize {
        self.data.pop().expect("data stack should not be empty")
    }

    fn pop_len(&mut self) -> NonZeroUsize {
        self.pop().try_into().unwrap()
    }

    fn pop_optional(&mut self) -> bool {
        self.optionals
            .pop()
            .expect("optionals stack should not be empty")
    }
}
