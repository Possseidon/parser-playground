use std::{borrow::Cow, ops::Range};

use crate::token::FixedTokenKind;

enum FormatterInput {
    Token(Range<usize>),
    Whitespace(Whitespace),
}

impl FormatterInput {
    fn token(&self) -> Range<usize> {
        if let Self::Token(token) = self {
            token.clone()
        } else {
            panic!("expected token")
        }
    }

    fn whitespace(&self) -> Whitespace {
        if let Self::Whitespace(whitespace) = self {
            *whitespace
        } else {
            panic!("expected whitespace")
        }
    }
}

/// Formats the code.
///
/// There are a few rules on `input`:
///
/// - It must start and end with a token.
/// - Tokens are separated by exactly one or two instances of whitespace.
fn format(code: &str, mut input: impl Iterator<Item = FormatterInput>) -> String {
    let mut result = String::new();

    let Some(first) = input.next() else {
        return result;
    };
    let first_token = first.token();

    // TODO: format first whitespace
    result += &code[0..first_token.start];

    result += &format_token(&code[first_token.clone()]);
    let mut prev_end = first_token.end;

    while let Some(next) = input.next() {
        let (whitespace, token) = whitespace_and_token(next, &mut input);

        // TODO: format whitespace according to `whitespace`
        result += &code[prev_end..token.start];
        result += &format_token(&code[token.clone()]);

        prev_end = token.end;
    }

    // TODO: format last whitespace
    result += &code[prev_end..];

    result
}

fn whitespace_and_token(
    next: FormatterInput,
    input: &mut impl Iterator<Item = FormatterInput>,
) -> (Whitespace, Range<usize>) {
    let whitespace = next.whitespace();
    let Some(next) = input.next() else {
        panic!("expected token");
    };
    match next {
        FormatterInput::Token(token) => (whitespace, token),
        FormatterInput::Whitespace(second_whitespace) => {
            let Some(next) = input.next() else {
                panic!("expected token");
            };
            (whitespace.merge(second_whitespace), next.token())
        }
    }
}

fn format_token(token: &str) -> Cow<str> {
    // TODO: normalize the token; e.g. 0XaBc to 0xABC
    token.into()
}

/// Specifies how whitespace should be handled in formatting.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Whitespace {
    /// Inserts whitespace.
    Insert {
        /// Ensures a singular space is present if no line break occurs.
        space: Space,
        /// Assigns a priority to determine optimal line break points in long lines.
        ///
        /// If multiple points have the same priority, the latest point wins.
        priority: i8,
        /// Indents the following line if a line break occurs.
        indent: bool,
    },
    /// Always inserts a line break.
    LineBreak {
        /// Add, remove or keep extra line breaks.
        extra: ExtraLineBreak,
    },
    /// Always inserts a line break and indents the following line.
    ///
    /// Extra line breaks are not allowed.
    Indent,
    /// Causes a line break if and only if a previous indent also caused a line break.
    ///
    /// Extra line breaks are not allowed.
    IndentContinuation {
        /// Inserts a space character if a line break is not inserted.
        space: bool,
        /// Makes sure a trailing token (e.g. `,`) exists if a line break is inserted.
        trailing_token: Option<TrailingToken>,
        /// Signifies the conclusion of an indentation block, potentially reducing the indentation level.
        undent: bool,
    },
}

impl Whitespace {
    const SPACE_NEVER: Self = Self::Insert {
        space: Space::Never,
        priority: 0,
        indent: false,
    };

    const SPACE_IF_NEEDED: Self = Self::Insert {
        space: Space::IfNeeded,
        priority: 0,
        indent: false,
    };

    const SPACE_IF_NEEDED_OR_INDENT: Self = Self::Insert {
        space: Space::IfNeeded,
        priority: 0,
        indent: true,
    };

    const SPACE_ALWAYS: Self = Self::Insert {
        space: Space::Always,
        priority: 0,
        indent: false,
    };

    const SPACE_ALWAYS_OR_INDENT: Self = Self::Insert {
        space: Space::Always,
        priority: 0,
        indent: true,
    };

    const SINGLE_LINE_BREAK: Self = Self::LineBreak {
        extra: ExtraLineBreak::Never,
    };

    const ADAPTIVE_LINE_BREAK: Self = Self::LineBreak {
        extra: ExtraLineBreak::Keep,
    };

    const DOUBLE_LINE_BREAK: Self = Self::LineBreak {
        extra: ExtraLineBreak::Always,
    };

    const INDENT: Self = Self::Indent;

    const INDENT_CONTINUATION: Self = Self::IndentContinuation {
        space: false,
        trailing_token: None,
        undent: false,
    };

    const UNDENT: Self = Self::IndentContinuation {
        space: false,
        trailing_token: None,
        undent: true,
    };

    const fn priority(self, priority: i8) -> Self {
        if let Self::Insert { space, indent, .. } = self {
            Self::Insert {
                space,
                priority,
                indent,
            }
        } else {
            panic!("cannot set priority")
        }
    }

    const fn trailing_token(self, trailing_token: TrailingToken) -> Self {
        if let Self::IndentContinuation { space, undent, .. } = self {
            Self::IndentContinuation {
                space,
                trailing_token: Some(trailing_token),
                undent,
            }
        } else {
            panic!("cannot set trailing token")
        }
    }

    const fn space(self) -> Self {
        if let Self::IndentContinuation {
            trailing_token,
            undent,
            ..
        } = self
        {
            Self::IndentContinuation {
                space: true,
                trailing_token,
                undent,
            }
        } else {
            panic!("cannot set space")
        }
    }

    const fn merge(self, other: Self) -> Self {
        todo!()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TrailingToken {
    space: bool,
    kind: FixedTokenKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Space {
    /// Never inserts a space, even if it changes semantic meaning for the lexer.
    ///
    /// Mainly a workaround for lambda parameters, where `| |` and `||` are semantically equivalent.
    Never,
    /// Inserts a space only if necessary by the lexer.
    ///
    /// This should be used instead of [`Space::Never`] in most cases.
    IfNeeded,
    /// Always inserts a space.
    Always,
}

/// Add, remove or keep extra line breaks.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ExtraLineBreak {
    /// Removes any extra line breaks.
    Never,
    /// Keeps up to one extra line break.
    Keep,
    /// Adds a single extra line break.
    Always,
}
