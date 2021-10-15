use std::fmt::Debug;
use thiserror::Error;

#[derive(Error, Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum PoisonError<K, G> {
    #[error("The lock with the key `{key:?}` is poisoned")]
    LockPoisoned { key: K, guard: G },
}

#[derive(Error, Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum UnpoisonError {
    #[error("Tried to unpoison a lock that wasn't poisoned")]
    NotPoisoned,

    #[error("Other threads are currently blocked on this mutex, we cannot unpoison it")]
    OtherThreadsBlockedOnMutex,
}
