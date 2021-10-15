use std::fmt::Debug;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum PoisonError<K> {
    #[error("The global mutex protecting the pool is poisoned")]
    PoolMutexPoisoned,

    // TODO Can we show the actual key in the message?
    #[error("The mutex with the key `{0:?}` is poisoned")]
    KeyPoisoned(K),
}
