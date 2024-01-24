pub(crate) mod lexer;
pub(crate) mod parser;

use thiserror::Error;

/// A generic error type used throughout the entire tiny parsing process.
///
/// It does intentionally not carry any useful information.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Error)]
#[error("input failed to parse; use a positioned parser for more accurate error messages")]
pub(crate) struct TinyError;

pub(crate) type TinyResult<T> = Result<T, TinyError>;
