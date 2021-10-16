use std::fmt::Debug;
use thiserror::Error;

/// A type of error which can be returned whenever a lock is acquired.
///
/// A lock is poisoned whenever a thread panics while a lock is held.
#[derive(Error, Debug, PartialEq, Eq, Hash, Clone, Copy)]
#[error("The lock with the key `{key:?}` couldn't be acquired because another thread panicked while holding this lock")]
pub struct PoisonError<K, G> {
    /// The key of the lock that was attempted to become locked
    pub key: K,
    pub(super) guard: G,
}

/// Errors that can be thrown by [LockPool::unpoison](super::LockPool::unpoison).
#[derive(Error, Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum UnpoisonError {
    /// Tried to unpoison a lock that wasn't poisoned
    #[error("Tried to unpoison a lock that wasn't poisoned")]
    NotPoisoned,

    /// At least one other thread is currently blocked on this mutex, we cannot unpoison it
    #[error("At least one other thread is currently blocked on this mutex, we cannot unpoison it")]
    OtherThreadsBlockedOnMutex,
}

/// Errors that can be thrown by [LockPool::try_lock](super::LockPool::try_lock).
#[derive(Error, Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum TryLockError<K, G> {
    /// The lock is poisoned, see [PoisonError]
    #[error(transparent)]
    Poisoned(PoisonError<K, G>),

    /// The lock could not be acquired at this time because the operation would otherwise block
    #[error(
        "The lock could not be acquired at this time because the operation would otherwise block"
    )]
    WouldBlock,
}
