

use std::convert::TryFrom;

#[derive(Debug, thiserror::Error)]
pub enum HataError {
    #[error("io error: {0}")]
    IoError(#[from] std::io::Error),

    #[error("utf8 error: {0}")]
    UtfError(#[from] std::str::Utf8Error),
}


