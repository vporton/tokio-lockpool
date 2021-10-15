use std::fmt::Debug;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum PoisonError<K> {
    #[error("The lock with the key `{0:?}` is poisoned")]
    LockPoisoned(K),
}
