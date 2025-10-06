use std::result;

pub type Result<T> = result::Result<T, Error>;

#[derive(Debug)]
pub enum Error {
    Empty,
    InsertFailed,
    RemoveFailed,
    SetValueFailed,
    GetValuefailed,
    IndexOutOfBound,
}

impl ToString for Error {
    fn to_string(&self) -> String {
        match self {
            Error::Empty => "Error::Empty".to_string(),
            Error::InsertFailed => "Error::InsertFailed".to_string(),
            Error::RemoveFailed => "Error::RemoveFailed".to_string(),
            Error::SetValueFailed => "Error::SetValueFailed".to_string(),
            Error::GetValuefailed => "Error::GetValueFailed".to_string(),
            Error::IndexOutOfBound => "Error::IndexOutOfBound".to_string(),
        }
    }
}
