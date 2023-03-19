use thiserror::Error;

pub type PDSAResult<T> = std::result::Result<T, PDSAError>;

#[derive(Debug, Error, PartialEq)]
pub enum PDSAError {
    #[error("Input value error: {0:?}")]
    InputError(String),
    #[error("Internal error: {0:?}")]
    Internal(String),
}
