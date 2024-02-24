use std::{fmt, marker::PhantomData, num::NonZeroUsize, ops::Range};

use bitvec::vec::BitVec;
use enum_map::Enum;
use paste::paste;
use smallvec::SmallVec;

use crate::{
    lexer::{CheckedLexer, LexerError},
    parser::ParseState,
};

pub(crate) trait FixedToken: Clone + Copy + fmt::Debug + PartialEq + Eq {
    const TEXT: &'static str;
}

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
                CheckedLexer, Expect, FixedToken, FixedTokenKind, LexerError, OptionalTokenSpan,
                ParseState, SmallVec, Style, TokenKind, TokenSpan, TokenSpanRepetition,
                TokenStorage,
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
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub(crate) struct $Kind;

        impl FixedToken for $Kind {
            const TEXT: &'static str = FixedTokenKind::$Kind.text();
        }

        impl<S: Style> TokenStorage<S> for $Kind {
            type Required = S::FixedRequired<Self>;
            type Optional = S::FixedOptional<Self>;
            type Repetition = S::FixedRepetition<Self>;
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
                S::push_fixed_required::<Self>(parser, expect)
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
                S::push_fixed_optional::<Self>(parser, TokenKind::$Kind, expect)
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
                S::push_fixed_repetition::<Self>(parser, TokenKind::$Kind, expect)
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
    type Required: RequiredToken;
    type Optional: OptionalToken;
    type Repetition: TokenRepetition;
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

pub(crate) trait Pos:
    Clone + Copy + fmt::Debug + Default + PartialEq + Eq + TryInto<usize> + From<usize>
{
    const FULL: bool;
}

impl Pos for usize {
    const FULL: bool = true;
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct NoPos;

impl TryFrom<NoPos> for usize {
    type Error = ();

    fn try_from(_value: NoPos) -> Result<Self, Self::Error> {
        Err(())
    }
}

impl From<usize> for NoPos {
    fn from(_value: usize) -> Self {
        Self
    }
}

impl Pos for NoPos {
    const FULL: bool = false;
}

pub(crate) trait Style: Clone + fmt::Debug + PartialEq + Eq {
    type FixedRequired<T: FixedToken>: RequiredToken;
    type FixedOptional<T: FixedToken>: OptionalToken;
    type FixedRepetition<T: FixedToken>: TokenRepetition;

    type Pos: Pos;

    fn fixed_required<T: FixedToken>(
        lexer: &mut CheckedLexer,
        expect: Expect,
    ) -> Result<Self::FixedRequired<T>, LexerError>;

    fn push_fixed_required<T: FixedToken>(
        state: &mut ParseState<Self>,
        expect: Expect,
    ) -> Result<(), LexerError>;

    fn pop_fixed_required<T: FixedToken>(state: &mut ParseState<Self>) -> Self::FixedRequired<T>;

    fn fixed_optional<T: FixedToken>(
        lexer: &mut CheckedLexer,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedOptional<T>, LexerError>;

    fn push_fixed_optional<T: FixedToken>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), LexerError>;

    fn pop_fixed_optional<T: FixedToken>(state: &mut ParseState<Self>) -> Self::FixedOptional<T>;

    fn fixed_repetition<T: FixedToken>(
        lexer: &mut CheckedLexer,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedRepetition<T>, LexerError>;

    fn push_fixed_repetition<T: FixedToken>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), LexerError>;

    fn pop_fixed_repetition<T: FixedToken>(
        state: &mut ParseState<Self>,
    ) -> Self::FixedRepetition<T>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Tiny;

impl Style for Tiny {
    type FixedRequired<T: FixedToken> = TinyToken<T>;
    type FixedOptional<T: FixedToken> = TinyOptionalToken<T>;
    type FixedRepetition<T: FixedToken> = TinyTokenRepetition<T>;

    type Pos = NoPos;

    fn fixed_required<T: FixedToken>(
        lexer: &mut CheckedLexer,
        expect: Expect,
    ) -> Result<Self::FixedRequired<T>, LexerError> {
        lexer.next(expect)?;
        Ok(TinyToken {
            _phantom: PhantomData,
        })
    }

    fn push_fixed_required<T: FixedToken>(
        state: &mut ParseState<Self>,
        expect: Expect,
    ) -> Result<(), LexerError> {
        state.lexer.next(expect)?;
        // pushing nothing
        Ok(())
    }

    fn pop_fixed_required<T: FixedToken>(_state: &mut ParseState<Self>) -> Self::FixedRequired<T> {
        // pop nothing
        TinyToken {
            _phantom: PhantomData,
        }
    }

    fn fixed_optional<T: FixedToken>(
        lexer: &mut CheckedLexer,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedOptional<T>, LexerError> {
        let some = lexer.matches(kind);
        if some {
            lexer.next(expect)?;
        }
        Ok(TinyOptionalToken {
            some,
            _phantom: PhantomData,
        })
    }

    fn push_fixed_optional<T: FixedToken>(
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

    fn pop_fixed_optional<T: FixedToken>(state: &mut ParseState<Self>) -> Self::FixedOptional<T> {
        TinyOptionalToken {
            some: state.tokens.pop_tiny_fixed_optional(),
            _phantom: PhantomData,
        }
    }

    fn fixed_repetition<T: FixedToken>(
        lexer: &mut CheckedLexer,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedRepetition<T>, LexerError> {
        let mut count = 0;
        while lexer.matches(kind) {
            count += 1;
            lexer.next(expect)?;
        }
        Ok(TinyTokenRepetition {
            count,
            _phantom: PhantomData,
        })
    }

    fn push_fixed_repetition<T: FixedToken>(
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

    fn pop_fixed_repetition<T: FixedToken>(
        state: &mut ParseState<Self>,
    ) -> Self::FixedRepetition<T> {
        TinyTokenRepetition {
            count: state.tokens.pop_tiny_fixed_repetition(),
            _phantom: PhantomData,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Full;

impl Style for Full {
    type FixedRequired<T: FixedToken> = FixedTokenSpan<T>;
    type FixedOptional<T: FixedToken> = FixedOptionalTokenSpan<T>;
    type FixedRepetition<T: FixedToken> = FixedTokenSpanRepetition<T>;

    type Pos = usize;

    fn fixed_required<T: FixedToken>(
        lexer: &mut CheckedLexer,
        expect: Expect,
    ) -> Result<Self::FixedRequired<T>, LexerError> {
        let pos = lexer.pos();
        lexer.next(expect)?;
        Ok(FixedTokenSpan {
            pos,
            _phantom: PhantomData,
        })
    }

    fn push_fixed_required<T: FixedToken>(
        state: &mut ParseState<Self>,
        expect: Expect,
    ) -> Result<(), LexerError> {
        state
            .tokens
            .push_fixed(Self::fixed_required::<T>(&mut state.lexer, expect)?);
        Ok(())
    }

    fn pop_fixed_required<T: FixedToken>(state: &mut ParseState<Self>) -> Self::FixedRequired<T> {
        state.tokens.pop_fixed()
    }

    fn fixed_optional<T: FixedToken>(
        lexer: &mut CheckedLexer,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedOptional<T>, LexerError> {
        let pos = lexer.pos();
        let some = lexer.matches(kind);
        if some {
            lexer.next(expect)?;
        }
        Ok(FixedOptionalTokenSpan {
            pos,
            some,
            _phantom: PhantomData,
        })
    }

    fn push_fixed_optional<T: FixedToken>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), LexerError> {
        state.tokens.push_fixed_optional(Self::fixed_optional::<T>(
            &mut state.lexer,
            kind,
            expect,
        )?);
        Ok(())
    }

    fn pop_fixed_optional<T: FixedToken>(state: &mut ParseState<Self>) -> Self::FixedOptional<T> {
        state.tokens.pop_fixed_optional()
    }

    fn fixed_repetition<T: FixedToken>(
        lexer: &mut CheckedLexer,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<Self::FixedRepetition<T>, LexerError> {
        let pos = lexer.pos();
        let mut tokens = SmallVec::new();
        while lexer.matches(kind) {
            tokens.push(Self::fixed_required(lexer, expect)?);
        }
        Ok(FixedTokenSpanRepetition {
            pos,
            tokens,
            _phantom: PhantomData,
        })
    }

    fn push_fixed_repetition<T: FixedToken>(
        state: &mut ParseState<Self>,
        kind: TokenKind,
        expect: Expect,
    ) -> Result<(), LexerError> {
        state
            .tokens
            .push_fixed_repetition(Self::fixed_repetition::<T>(&mut state.lexer, kind, expect)?);
        Ok(())
    }

    fn pop_fixed_repetition<T: FixedToken>(
        state: &mut ParseState<Self>,
    ) -> Self::FixedRepetition<T> {
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

pub(crate) trait RequiredToken:
    Clone + Copy + fmt::Debug + PartialEq + Eq + TryCodeSpan
{
}

impl<T: Clone + Copy + fmt::Debug + PartialEq + Eq + TryCodeSpan> RequiredToken for T {}

pub(crate) trait OptionalToken:
    Clone + Copy + fmt::Debug + PartialEq + Eq + TryCodeSpan
{
    fn is_some(&self) -> bool;
}

pub(crate) trait TokenRepetition: Clone + fmt::Debug + PartialEq + Eq + TryCodeSpan {
    fn count(&self) -> usize;
}

pub(crate) trait CodeSpan {
    fn code_span(&self) -> Range<usize>;
}

pub(crate) trait TryCodeSpan {
    fn try_code_span(&self) -> Option<Range<usize>>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TokenSpan {
    pub(crate) pos: usize,
    pub(crate) len: NonZeroUsize,
}

impl CodeSpan for TokenSpan {
    fn code_span(&self) -> Range<usize> {
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

impl OptionalToken for OptionalTokenSpan {
    fn is_some(&self) -> bool {
        self.len.is_some()
    }
}

impl CodeSpan for OptionalTokenSpan {
    fn code_span(&self) -> Range<usize> {
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

impl TokenRepetition for TokenSpanRepetition {
    fn count(&self) -> usize {
        self.tokens.len()
    }
}

impl CodeSpan for TokenSpanRepetition {
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
pub(crate) struct FixedTokenSpan<T: FixedToken> {
    pub(crate) pos: usize,
    _phantom: PhantomData<fn() -> T>,
}

impl<T: FixedToken> CodeSpan for FixedTokenSpan<T> {
    fn code_span(&self) -> Range<usize> {
        Range {
            start: self.pos,
            end: self.pos + T::TEXT.len(),
        }
    }
}

impl<T: FixedToken> TryCodeSpan for FixedTokenSpan<T> {
    fn try_code_span(&self) -> Option<Range<usize>> {
        Some(self.code_span())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FixedOptionalTokenSpan<T: FixedToken> {
    pub(crate) pos: usize,
    pub(crate) some: bool,
    _phantom: PhantomData<fn() -> T>,
}

impl<T: FixedToken> OptionalToken for FixedOptionalTokenSpan<T> {
    fn is_some(&self) -> bool {
        self.some
    }
}

impl<T: FixedToken> CodeSpan for FixedOptionalTokenSpan<T> {
    fn code_span(&self) -> Range<usize> {
        Range {
            start: self.pos,
            end: self.pos + if self.some { T::TEXT.len() } else { 0 },
        }
    }
}

impl<T: FixedToken> TryCodeSpan for FixedOptionalTokenSpan<T> {
    fn try_code_span(&self) -> Option<Range<usize>> {
        Some(self.code_span())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FixedTokenSpanRepetition<T: FixedToken> {
    pub(crate) pos: usize,
    pub(crate) tokens: SmallVec<[FixedTokenSpan<T>; 1]>,
    _phantom: PhantomData<fn() -> T>,
}

impl<T: FixedToken> TokenRepetition for FixedTokenSpanRepetition<T> {
    fn count(&self) -> usize {
        self.tokens.len()
    }
}

impl<T: FixedToken> CodeSpan for FixedTokenSpanRepetition<T> {
    fn code_span(&self) -> Range<usize> {
        Range {
            start: self.pos,
            end: self.pos
                + self
                    .tokens
                    .last()
                    .map_or(0, |token| token.pos - self.pos + T::TEXT.len()),
        }
    }
}

impl<T: FixedToken> TryCodeSpan for FixedTokenSpanRepetition<T> {
    fn try_code_span(&self) -> Option<Range<usize>> {
        Some(self.code_span())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TinyToken<T: FixedToken> {
    _phantom: PhantomData<fn() -> T>,
}

impl<T: FixedToken> TryCodeSpan for TinyToken<T> {
    fn try_code_span(&self) -> Option<Range<usize>> {
        None
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TinyOptionalToken<T: FixedToken> {
    pub(crate) some: bool,
    _phantom: PhantomData<fn() -> T>,
}

impl<T: FixedToken> OptionalToken for TinyOptionalToken<T> {
    fn is_some(&self) -> bool {
        self.some
    }
}

impl<T: FixedToken> TryCodeSpan for TinyOptionalToken<T> {
    fn try_code_span(&self) -> Option<Range<usize>> {
        None
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TinyTokenRepetition<T: FixedToken> {
    pub(crate) count: usize,
    _phantom: PhantomData<fn() -> T>,
}

impl<T: FixedToken> TokenRepetition for TinyTokenRepetition<T> {
    fn count(&self) -> usize {
        self.count
    }
}

impl<T: FixedToken> TryCodeSpan for TinyTokenRepetition<T> {
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

    pub(crate) fn push_fixed<T: FixedToken>(&mut self, token: FixedTokenSpan<T>) {
        self.data.push(token.pos);
    }

    pub(crate) fn pop_fixed<T: FixedToken>(&mut self) -> FixedTokenSpan<T> {
        FixedTokenSpan {
            pos: self.pop(),
            _phantom: PhantomData,
        }
    }

    pub(crate) fn push_fixed_optional<T: FixedToken>(&mut self, token: FixedOptionalTokenSpan<T>) {
        self.optionals.push(token.some);
        self.data.push(token.pos);
    }

    pub(crate) fn pop_fixed_optional<T: FixedToken>(&mut self) -> FixedOptionalTokenSpan<T> {
        FixedOptionalTokenSpan {
            pos: self.pop(),
            some: self.pop_optional(),
            _phantom: PhantomData,
        }
    }

    pub(crate) fn push_tiny_fixed_optional(&mut self, some: bool) {
        self.optionals.push(some);
    }

    pub(crate) fn pop_tiny_fixed_optional(&mut self) -> bool {
        self.pop_optional()
    }

    pub(crate) fn push_fixed_repetition<T: FixedToken>(
        &mut self,
        repetition: FixedTokenSpanRepetition<T>,
    ) {
        self.data
            .extend(repetition.tokens.iter().rev().map(|token| token.pos));
        self.data.push(repetition.tokens.len());
        self.data.push(repetition.pos);
    }

    pub(crate) fn pop_fixed_repetition<T: FixedToken>(&mut self) -> FixedTokenSpanRepetition<T> {
        FixedTokenSpanRepetition {
            pos: self.pop(),
            tokens: {
                (0..self.pop())
                    .map(|_| FixedTokenSpan {
                        pos: self.pop(),
                        _phantom: PhantomData,
                    })
                    .collect()
            },
            _phantom: PhantomData,
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
