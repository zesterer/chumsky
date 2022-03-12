use super::*;

pub trait Error<T> {
    fn create() -> Self;
}

impl<T> Error<T> for () {
    fn create() -> Self {}
}
