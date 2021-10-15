use std::fmt::Debug;
use thiserror::Error;

#[derive(Error, Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum PoisonError<K> {
    #[error("The lock with the key `{0:?}` is poisoned")]
    LockPoisoned(K),
}

#[derive(Error, Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum UnpoisonError {
    #[error("Tried to unpoison a lock that wasn't poisoned")]
    NotPoisoned,
}
