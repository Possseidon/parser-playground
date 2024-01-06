use std::{fmt, marker::PhantomData, num::NonZeroUsize};

use enum_map::Enum;
use paste::paste;
use smol_str::SmolStr;

use crate::lexer::PositionedLexerToken;

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
            /// Returns symbols and keywords as text. Panics for dynamic tokens like identifiers.
            const fn text(self) -> &'static str {
                match self {
                    $( Self::$Dynamic )|* => panic!("dynamic tokens have no static text"),
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

        pub(crate) mod token {
            use super::{Kind, Style, TokenKind};

            $(
                #[derive(Clone, Copy, Debug, PartialEq, Eq)]
                pub(crate) struct $Dynamic;

                impl Kind for $Dynamic {
                    const KIND: TokenKind = TokenKind::$Dynamic;
                    type Repr<S: Style> = S::Dynamic<Self>;
                }
            )*

            $(
                #[derive(Clone, Copy, Debug, PartialEq, Eq)]
                pub(crate) struct $Keyword;

                impl Kind for $Keyword {
                    const KIND: TokenKind = TokenKind::$Keyword;
                    type Repr<S: Style> = S::Fixed<Self>;
                }
            )*

            $(
                #[derive(Clone, Copy, Debug, PartialEq, Eq)]
                pub(crate) struct $Symbol;

                impl Kind for $Symbol {
                    const KIND: TokenKind = TokenKind::$Symbol;
                    type Repr<S: Style> = S::Fixed<Self>;
                }
            )*

            $(
                #[derive(Clone, Copy, Debug, PartialEq, Eq)]
                pub(crate) struct $Char;

                impl Kind for $Char {
                    const KIND: TokenKind = TokenKind::$Char;
                    type Repr<S: Style> = S::Fixed<Self>;
                }
            )*
        }
    };
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

impl TokenKind {
    /// Returns the length of symbols and keywords. Panics for dynamic tokens like identifiers.
    pub(crate) const fn len(self) -> NonZeroUsize {
        match NonZeroUsize::new(self.text().len()) {
            Some(val) => val,
            None => panic!(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TinyFixedTokenRepr<K: Kind> {
    _kind: PhantomData<*const K>,
}

impl<K: Kind> TinyToken for TinyFixedTokenRepr<K> {
    fn new(_text: SmolStr) -> Self {
        Self { _kind: PhantomData }
    }

    fn text(self) -> SmolStr {
        K::KIND.text().into()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TinyDynamicTokenRepr<K: Kind> {
    text: SmolStr,
    _kind: PhantomData<*const K>,
}

impl<K: Kind> TinyToken for TinyDynamicTokenRepr<K> {
    fn new(text: SmolStr) -> Self {
        Self {
            text,
            _kind: PhantomData,
        }
    }

    fn text(self) -> SmolStr {
        self.text
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PositionedFixedTokenRepr<K: Kind> {
    pos: usize,
    trailing_whitespace_len: usize,
    _kind: PhantomData<*const K>,
}

impl<K: Kind> PositionedToken for PositionedFixedTokenRepr<K> {
    fn new(token: PositionedLexerToken) -> Self {
        Self {
            pos: token.pos,
            trailing_whitespace_len: token.trailing_whitespace_len,
            _kind: PhantomData,
        }
    }

    fn pos(self) -> usize {
        self.pos
    }

    fn len(self) -> NonZeroUsize {
        K::KIND.len()
    }

    fn trailing_whitespace_len(self) -> usize {
        self.trailing_whitespace_len
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PositionedDynamicTokenRepr<K: Kind> {
    pos: usize,
    len: NonZeroUsize,
    trailing_whitespace_len: usize,
    _kind: PhantomData<*const K>,
}

impl<K: Kind> PositionedToken for PositionedDynamicTokenRepr<K> {
    fn new(token: PositionedLexerToken) -> Self {
        Self {
            pos: token.pos,
            len: token.len,
            trailing_whitespace_len: token.trailing_whitespace_len,
            _kind: PhantomData,
        }
    }

    fn pos(self) -> usize {
        self.pos
    }

    fn len(self) -> NonZeroUsize {
        self.len
    }

    fn trailing_whitespace_len(self) -> usize {
        self.trailing_whitespace_len
    }
}

/// Whether the token is [`Tiny`] or [`Positioned`].
///
/// Trait bounds on [`Clone`] and [`Debug`] are a hack to simplify `#[derive(Clone, Debug)]` on AST
/// node types.
pub(crate) trait Style: Clone + fmt::Debug + PartialEq + std::cmp::Eq {
    type Fixed<K: Kind>: Clone + fmt::Debug + PartialEq + std::cmp::Eq;
    type Dynamic<K: Kind>: Clone + fmt::Debug + PartialEq + std::cmp::Eq;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Tiny;

impl Style for Tiny {
    type Fixed<K: Kind> = TinyFixedTokenRepr<K>;
    type Dynamic<K: Kind> = TinyDynamicTokenRepr<K>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Positioned;

impl Style for Positioned {
    type Fixed<K: Kind> = PositionedFixedTokenRepr<K>;
    type Dynamic<K: Kind> = PositionedDynamicTokenRepr<K>;
}

pub(crate) trait Kind: Clone + Copy + fmt::Debug + PartialEq + std::cmp::Eq {
    const KIND: TokenKind;
    type Repr<S: Style>: Clone + fmt::Debug + PartialEq + std::cmp::Eq;
}

/// Very small memory footprint for parsing, but is not capable of producing good error messages.
///
/// This is intended be used for "optimistic parsing". When you already know up front, that the
/// source code *should* be valid, this is more efficient.
///
/// Unlike [`PositionedToken`], this does not require the original source code. However, to make up
/// for this, it uses [`SmolStr`] internally, which means not all tokens can be [`Copy`] (since
/// [`SmolStr`] itself is not [`Copy`]). Clones are still very cheap though (usually just as cheap
/// as [`Copy`], worst case incrementing the ref-count of an [`Arc`](std::sync::Arc) for e.g. long
/// identifiers).
///
/// Formatting is not supported, since this representation loses all information about whitespace,
/// including comments.
pub(crate) trait TinyToken: Clone {
    fn new(text: SmolStr) -> Self;
    fn text(self) -> SmolStr;
}

/// Positioned tokens that point at the original source code.
///
/// This is required for proper error messages.
pub(crate) trait PositionedToken: Copy {
    /// Assumes that the current token has the correct kind.
    ///
    /// This check should already have happened via `EXPECTED_TOKENS`.
    fn new(token: PositionedLexerToken) -> Self;
    fn pos(self) -> usize;
    fn len(self) -> NonZeroUsize;
    fn trailing_whitespace_len(self) -> usize;
}

pub(crate) struct Token<K: Kind, S: Style>(K::Repr<S>);

impl<K: Kind, S: Style> fmt::Debug for Token<K, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Token").field(&self.0).finish()
    }
}

impl<K: Kind, S: Style> Clone for Token<K, S> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<K: Kind, S: Style> Copy for Token<K, S> where K::Repr<S>: Copy {}

impl<K: Kind, S: Style> PartialEq for Token<K, S>
where
    K::Repr<S>: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<K: Kind, S: Style> std::cmp::Eq for Token<K, S> where K::Repr<S>: std::cmp::Eq {}

impl<K: Kind> TinyToken for Token<K, Tiny>
where
    K::Repr<Tiny>: TinyToken,
{
    fn new(text: SmolStr) -> Self {
        Self(<K::Repr<Tiny> as TinyToken>::new(text))
    }

    fn text(self) -> SmolStr {
        self.0.text()
    }
}

impl<K: Kind> PositionedToken for Token<K, Positioned>
where
    K::Repr<Positioned>: PositionedToken,
{
    fn new(token: PositionedLexerToken) -> Self {
        Self(<K::Repr<Positioned> as PositionedToken>::new(token))
    }

    fn pos(self) -> usize {
        self.0.pos()
    }

    fn len(self) -> NonZeroUsize {
        self.0.len()
    }

    fn trailing_whitespace_len(self) -> usize {
        self.0.trailing_whitespace_len()
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
