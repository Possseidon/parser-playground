use std::{fmt, num::NonZeroUsize};

use enum_map::Enum;
use paste::paste;
use smallvec::SmallVec;
use smol_str::SmolStr;

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
            use crate::{
                tiny::{
                    TinyResult,
                    lexer::CheckedTinyLexer,
                    parser::TinyParseState,
                },
            };

            use super::{Expect, Style, TokenStorage, Tiny, TokenKind, TokenSet};

            $(
                pub(crate) struct $Dynamic;

                impl<S: Style> TokenStorage<S> for $Dynamic {
                    type Required = S::DynamicRequired;
                    type Optional = S::DynamicOptional;
                    type Repetition = S::DynamicRepetition;
                }

                impl $Dynamic {
                    pub(crate) fn parse_required(lexer: &mut CheckedTinyLexer, expect: Expect) -> TinyResult<<Self as TokenStorage<Tiny>>::Required> {
                        lexer.next(expect)
                    }

                    pub(crate) fn parse_optional(lexer: &mut CheckedTinyLexer, expect: Expect) -> TinyResult<<Self as TokenStorage<Tiny>>::Optional> {
                        Ok(if lexer.matches(TokenSet::from_kind(TokenKind::$Dynamic)) {
                            Some(lexer.next(expect)?)
                        } else {
                            None
                        })
                    }

                    pub(crate) fn parse_repetition(lexer: &mut CheckedTinyLexer, expect: Expect) -> TinyResult<<Self as TokenStorage<Tiny>>::Repetition> {
                        let mut result = <Self as TokenStorage<Tiny>>::Repetition::new();
                        while lexer.matches(TokenSet::from_kind(TokenKind::$Dynamic)) {
                            result.push(lexer.next(expect)?);
                        }
                        Ok(result)
                    }

                    pub(crate) fn tiny_push_required(state: &mut TinyParseState, expect: Expect) -> TinyResult<()> {
                        state.tokens.push_dynamic(state.lexer.next(expect)?);
                        Ok(())
                    }

                    pub(crate) fn tiny_pop_required(state: &mut TinyParseState) -> <Self as TokenStorage<Tiny>>::Required {
                        state.tokens.pop_dynamic()
                    }

                    pub(crate) fn tiny_push_optional(state: &mut TinyParseState, expect: Expect) -> TinyResult<()> {
                        if state.lexer.matches(TokenSet::from_kind(TokenKind::$Dynamic)) {
                            state.tokens.push_dynamic_some(state.lexer.next(expect)?);
                        } else {
                            state.tokens.push_none();
                        }
                        Ok(())
                    }

                    pub(crate) fn tiny_pop_optional(state: &mut TinyParseState) -> <Self as TokenStorage<Tiny>>::Optional {
                        state.tokens.pop_dynamic_optional()
                    }

                    pub(crate) fn tiny_push_repetition(state: &mut TinyParseState, expect: Expect) -> TinyResult<()> {
                        state.tokens.start_dynamic_repetition();
                        while state.lexer.matches(TokenSet::from_kind(TokenKind::$Dynamic)) {
                            state.tokens.push_dynamic(state.lexer.next(expect)?);
                        }
                        Ok(())
                    }

                    pub(crate) fn tiny_pop_repetition(state: &mut TinyParseState) -> <Self as TokenStorage<Tiny>>::Repetition {
                        state.tokens.pop_dynamic_repetition().collect()
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

        impl<S: Style> TokenStorage<S> for $Kind {
            type Required = S::FixedRequired;
            type Optional = S::FixedOptional;
            type Repetition = S::FixedRepetition;
        }

        impl $Kind {
            pub(crate) fn parse_required(lexer: &mut CheckedTinyLexer, expect: Expect) -> TinyResult<<Self as TokenStorage<Tiny>>::Required> {
                lexer.next(expect)?;
                Ok(())
            }

            pub(crate) fn parse_optional(lexer: &mut CheckedTinyLexer, expect: Expect) -> TinyResult<<Self as TokenStorage<Tiny>>::Optional> {
                let result = lexer.matches(TokenSet::from_kind(TokenKind::$Kind));
                if result {
                    lexer.next(expect)?;
                }
                Ok(result)
            }

            pub(crate) fn parse_repetition(lexer: &mut CheckedTinyLexer, expect: Expect) -> TinyResult<<Self as TokenStorage<Tiny>>::Repetition> {
                let mut count = 0;
                while lexer.matches(TokenSet::from_kind(TokenKind::$Kind)) {
                    lexer.next(expect)?;
                    count += 1;
                }
                Ok(count)
            }

            pub(crate) fn tiny_push_required(state: &mut TinyParseState, expect: Expect) -> TinyResult<()> {
                state.lexer.next(expect)?;
                Ok(())
            }

            pub(crate) fn tiny_pop_required(state: &mut TinyParseState) -> <Self as TokenStorage<Tiny>>::Required {}

            pub(crate) fn tiny_push_optional(state: &mut TinyParseState, expect: Expect) -> TinyResult<()> {
                if state.lexer.matches(TokenSet::from_kind(TokenKind::$Kind)) {
                    state.lexer.next(expect)?;
                    state.tokens.push_fixed_some();
                } else {
                    state.tokens.push_none();
                }
                Ok(())
            }

            pub(crate) fn tiny_pop_optional(state: &mut TinyParseState) -> <Self as TokenStorage<Tiny>>::Optional {
                state.tokens.pop_fixed_optional()
            }

            pub(crate) fn tiny_push_repetition(state: &mut TinyParseState, expect: Expect) -> TinyResult<()> {
                let mut count = 0;
                while state.lexer.matches(TokenSet::from_kind(TokenKind::$Kind)) {
                    state.lexer.next(expect)?;
                    count += 1;
                }
                state.tokens.push_fixed_repetition(count);
                Ok(())
            }

            pub(crate) fn tiny_pop_repetition(state: &mut TinyParseState) -> <Self as TokenStorage<Tiny>>::Repetition {
                state.tokens.pop_fixed_repetition()
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
    type FixedRequired: Clone + fmt::Debug + PartialEq + Eq;
    type FixedOptional: Clone + fmt::Debug + PartialEq + Eq;
    type FixedRepetition: Clone + fmt::Debug + PartialEq + Eq;

    type DynamicRequired: Clone + fmt::Debug + PartialEq + Eq;
    type DynamicOptional: Clone + fmt::Debug + PartialEq + Eq;
    type DynamicRepetition: Clone + fmt::Debug + PartialEq + Eq;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Tiny;

impl Style for Tiny {
    type FixedRequired = ();
    type FixedOptional = bool;
    type FixedRepetition = usize;

    type DynamicRequired = SmolStr;
    type DynamicOptional = Option<SmolStr>;
    type DynamicRepetition = SmallVec<[SmolStr; 1]>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Positioned;

impl Style for Positioned {
    type FixedRequired = ();
    type FixedOptional = ();
    type FixedRepetition = ();

    type DynamicRequired = ();
    type DynamicOptional = ();
    type DynamicRepetition = ();
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
