use std::fmt::Debug;
use thiserror::Error;

/// A type of error which can be returned whenever a lock is acquired.
///
/// A lock is poisoned whenever a thread panics while a lock is held.
#[derive(Error, Debug, PartialEq, Eq, Hash, Clone, Copy)]
#[error("The lock with the key `{key:?}` couldn't be acquired because another thread panicked while holding this lock")]
pub struct PoisonError<K, G> {
    pub key: K,
    pub(super) guard: G,
}

/// Errors that can be thrown by [LockPool::unpoison](super::LockPool::unpoison).
#[derive(Error, Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum UnpoisonError {
    #[error("Tried to unpoison a lock that wasn't poisoned")]
    NotPoisoned,

    #[error("Other threads are currently blocked on this mutex, we cannot unpoison it")]
    OtherThreadsBlockedOnMutex,
}

/// Errors that can be thrown by [LockPool::try_lock](super::LockPool::try_lock).
#[derive(Error, Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum TryLockError<K, G> {
    #[error(transparent)]
    Poisoned(#[from] PoisonError<K, G>),

    #[error(
        "The lock could not be acquired at this time because the operation would otherwise block"
    )]
    WouldBlock,
}
