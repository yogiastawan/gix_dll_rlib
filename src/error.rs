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
    NodeNotAssociated,
}

impl ToString for Error {
    fn to_string(&self) -> String {
        let error = match self {
            Error::Empty => "Error::Empty",
            Error::InsertFailed => "Error::InsertFailed",
            Error::RemoveFailed => "Error::RemoveFailed",
            Error::SetValueFailed => "Error::SetValueFailed",
            Error::GetValuefailed => "Error::GetValueFailed",
            Error::IndexOutOfBound => "Error::IndexOutOfBound",
            Error::NodeNotAssociated => "NodeNotAssociated",
        };

        error.to_string()
    }
}
