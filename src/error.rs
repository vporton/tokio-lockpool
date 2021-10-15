use std::fmt::Debug;
use thiserror::Error;

#[derive(Error, Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum PoisonError<K, G> {
    #[error("The lock with the key `{key:?}` couldn't be acquired because another thread panicked while holding this lock")]
    LockPoisoned { key: K, guard: G },
}

#[derive(Error, Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum UnpoisonError {
    #[error("Tried to unpoison a lock that wasn't poisoned")]
    NotPoisoned,

    #[error("Other threads are currently blocked on this mutex, we cannot unpoison it")]
    OtherThreadsBlockedOnMutex,
}

#[derive(Error, Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum TryLockError<K, G> {
    #[error(transparent)]
    Poisoned(#[from] PoisonError<K, G>),

    #[error(
        "The lock could not be acquired at this time because the operation would otherwise block"
    )]
    WouldBlock,
}
