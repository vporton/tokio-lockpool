use owning_ref::OwningHandle;
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::{Arc, Mutex, MutexGuard};

use super::LockPool;

/// A RAII implementation of a scoped lock for locks from a [LockPool]. When this structure is dropped (falls out of scope), the lock will be unlocked.
pub struct Guard<'a, K>
where
    K: Eq + PartialEq + Hash + Clone + Debug,
{
    pool: &'a LockPool<K>,
    key: K,
    guard: Option<OwningHandle<Arc<Mutex<()>>, MutexGuard<'a, ()>>>,
}

impl<'a, K> Guard<'a, K>
where
    K: Eq + PartialEq + Hash + Clone + Debug,
{
    pub(super) fn new(
        pool: &'a LockPool<K>,
        key: K,
        guard: OwningHandle<Arc<Mutex<()>>, MutexGuard<'a, ()>>,
    ) -> Self {
        Self {
            pool,
            key,
            guard: Some(guard),
        }
    }
}

impl<'a, K> Drop for Guard<'a, K>
where
    K: Eq + PartialEq + Hash + Clone + Debug,
{
    fn drop(&mut self) {
        let guard = self
            .guard
            .take()
            .expect("The self.guard field must always be set unless this was already destructed");
        self.pool._unlock(&self.key, guard).unwrap();
    }
}
