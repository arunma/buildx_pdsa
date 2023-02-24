use thiserror::Error;

pub type ProllyResult<T> = std::result::Result<T, ProllyError>;

#[derive(Debug, Error, PartialEq)]
pub enum ProllyError {
    #[error("Input value error: {0:?}")]
    Input(String),
    #[error("Internal error: {0:?}")]
    Internal(String),
}
