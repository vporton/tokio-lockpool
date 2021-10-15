use owning_ref::OwningHandle;
use std::fmt::{self, Debug};
use std::hash::Hash;
use std::sync::{Arc, Mutex, MutexGuard};

use super::LockPool;

/// A RAII implementation of a scoped lock for locks from a [LockPool]. When this structure is dropped (falls out of scope), the lock will be unlocked.
#[must_use = "if unused the Mutex will immediately unlock"]
pub struct Guard<'a, K>
where
    K: Eq + PartialEq + Hash + Clone + Debug,
{
    pool: &'a LockPool<K>,
    key: K,
    guard: Option<OwningHandle<Arc<Mutex<()>>, MutexGuard<'a, ()>>>,
    poisoned: bool,
}

impl<'a, K> Guard<'a, K>
where
    K: Eq + PartialEq + Hash + Clone + Debug,
{
    pub(super) fn new(
        pool: &'a LockPool<K>,
        key: K,
        guard: OwningHandle<Arc<Mutex<()>>, MutexGuard<'a, ()>>,
        poisoned: bool,
    ) -> Self {
        Self {
            pool,
            key,
            guard: Some(guard),
            poisoned,
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
        self.pool._unlock(&self.key, guard, self.poisoned);
    }
}

impl<'a, K> Debug for Guard<'a, K>
where
    K: Eq + PartialEq + Hash + Clone + Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Guard({:?})", self.key)
    }
}
