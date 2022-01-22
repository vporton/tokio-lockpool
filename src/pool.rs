use owning_ref::OwningHandle;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::{Arc, MutexGuard};
use tokio::sync::Mutex;

use super::{Guard, TryLockError};

/// This is a pool of locks where individual locks can be locked/unlocked by key. It initially considers all keys as "unlocked", but they can be locked
/// and if a second thread tries to acquire a lock for the same key, they will have to wait.
///
/// Under the hood, a [LockPool] is a [HashMap] of [Mutex]es, with some logic making sure there aren't any race conditions when accessing the hash map.
///
/// Example:
/// -----
/// ```
/// use lockpool::LockPool;
///
/// let pool = LockPool::new();
/// # (|| -> () {
/// let guard1 = pool.lock(4)?;
/// let guard2 = pool.lock(5)?;
///
/// // This next line would cause a deadlock or panic because `4` is already locked on this thread
/// // let guard3 = pool.lock(4)?;
///
/// // After dropping the corresponding guard, we can lock it again
/// std::mem::drop(guard1);
/// let guard3 = pool.lock(4)?;
/// # Ok(())
/// # })().unwrap();
/// ```
///
pub struct LockPool<K>
where
    K: Eq + PartialEq + Hash + Clone + Debug,
{
    currently_locked: Mutex<HashMap<K, Arc<Mutex<()>>>>,
}

impl<K> Default for LockPool<K>
where
    K: Eq + PartialEq + Hash + Clone + Debug,
{
    fn default() -> Self {
        Self {
            currently_locked: Mutex::new(HashMap::new()),
        }
    }
}

impl<K> LockPool<K>
where
    K: Eq + PartialEq + Hash + Clone + Debug,
{
    /// Create a new lock pool where no lock is locked
    pub fn new() -> Self {
        Self::default()
    }

    /// Return the number of locked locks
    pub fn num_locked(&self) -> usize {
        self._currently_locked().len()
    }

    /// Lock a lock by key.
    ///
    /// If the lock with this key is currently locked by a different thread, then the current thread blocks until it becomes available.
    /// Upon returning, the thread is the only thread with the lock held. A RAII guard is returned to allow scoped unlock
    /// of the lock. When the guard goes out of scope, the lock will be unlocked.
    ///
    /// The exact behavior on locking a lock in the thread which already holds the lock is left unspecified.
    /// However, this function will not return on the second call (it might panic or deadlock, for example).
    ///
    /// Errors
    /// -----
    /// If another user of this lock panicked while holding the lock, then this call will return an error once the lock is acquired.
    ///
    /// Panics
    /// -----
    /// This function might panic when called if the lock is already held by the current thread.
    ///
    /// Examples
    /// -----
    /// ```
    /// use lockpool::LockPool;
    ///
    /// let pool = LockPool::new();
    /// # (|| -> () {
    /// let guard1 = pool.lock(4).await;
    /// let guard2 = pool.lock(5).await;
    ///
    /// // This next line would cause a deadlock or panic because `4` is already locked on this thread
    /// // let guard3 = pool.lock(4)?;
    ///
    /// // After dropping the corresponding guard, we can lock it again
    /// std::mem::drop(guard1);
    /// let guard3 = pool.lock(4)?;
    /// # Ok(())
    /// # })().unwrap();
    /// ```
    pub fn lock(&self, key: K) -> Guard<'_, K> {
        let mutex = self._load_or_insert_mutex_for_key(&key);
        // Now we have an Arc::clone of the mutex for this key, and the global mutex is already unlocked so other threads can access the hash map.
        // The following blocks until the mutex for this key is acquired.
        self._lock(key, mutex)
    }

    /// Attempts to acquire the lock with the given key.
    ///
    /// If the lock could not be acquired at this time, then [Err] is returned. Otherwise, a RAII guard is returned.
    /// The lock will be unlocked when the guard is dropped.
    ///
    /// This function does not block.
    ///
    /// Errors
    /// -----
    /// - If the lock could not be acquired because it is already locked, then this call will return [TryLockError::WouldBlock].
    ///
    /// Examples
    /// -----
    /// ```
    /// use lockpool::{TryLockError, LockPool};
    ///
    /// let pool = LockPool::new();
    /// # (|| -> () {
    /// let guard1 = pool.lock(4).await;
    /// let guard2 = pool.lock(5).await;
    ///
    /// // This next line would cause a deadlock or panic because `4` is already locked on this thread
    /// let guard3 = pool.try_lock(4);
    /// assert!(matches!(guard3.unwrap_err(), TryLockError::WouldBlock));
    ///
    /// // After dropping the corresponding guard, we can lock it again
    /// std::mem::drop(guard1);
    /// let guard3 = pool.lock(4)?;
    /// # Ok(())
    /// # })().unwrap();
    /// ```
    pub fn try_lock(&self, key: K) -> Result<Guard<'_, K>, TryLockError> {
        let mutex = self._load_or_insert_mutex_for_key(&key);
        self._try_lock(key, mutex)
    }

    fn _currently_locked(&self) -> MutexGuard<'_, HashMap<K, Arc<Mutex<()>>>> {
        self.currently_locked
            .lock()
            .await;
    }

    fn _load_or_insert_mutex_for_key(&self, key: &K) -> Arc<Mutex<()>> {
        let mut currently_locked = self._currently_locked();
        if let Some(mutex) = currently_locked.get_mut(key).map(|a| Arc::clone(a)) {
            mutex
        } else {
            let insert_result = currently_locked.insert(key.clone(), Arc::new(Mutex::new(())));
            assert!(
                insert_result.is_none(),
                "We just checked that the entry doesn't exist, why does it exist now?"
            );
            currently_locked
                .get_mut(key)
                .map(|a| Arc::clone(a))
                .expect("We just inserted this")
        }
    }

    fn _lock(
        &self,
        key: K,
        mutex: Arc<Mutex<()>>,
    ) -> Guard<'_, K> {
        let guard = OwningHandle::new_with_fn(mutex, |mutex: *const Mutex<()>| {
            let mutex: &Mutex<()> = unsafe { &*mutex };
        });
        let guard = Guard::new(self, key, guard, false);
        Ok(guard)
    }

    fn _try_lock(
        &self,
        key: K,
        mutex: Arc<Mutex<()>>,
    ) -> Result<Guard<'_, K>, TryLockError> {
        let guard = OwningHandle::try_new(mutex, |mutex: *const Mutex<()>| {
            let mutex: &Mutex<()> = unsafe { &*mutex };
            match mutex.try_lock() {
                Ok(guard) => Ok(guard),
                Err(std::sync::TryLockError::WouldBlock) => Err(TryLockError::WouldBlock),
            }
        })?;
        let guard = Guard::new(self, key, guard, false);
        Ok(guard)
    }

    pub(super) fn _unlock(
        &self,
        key: &K,
        guard: OwningHandle<Arc<Mutex<()>>, MutexGuard<'_, ()>>,
    ) {
        let mut currently_locked = self._currently_locked();
        let mutex: &Arc<Mutex<()>> = currently_locked
            .get(key)
            .expect("This entry must exist or the guard passed in as a parameter shouldn't exist");
        std::mem::drop(guard);

        // Now the guard is dropped and the lock for this key is unlocked.
        // If there are any other Self::lock() calls for this key already running and
        // waiting for the mutex, they will be unblocked now and their guard
        // will be created.
        // But since we still have the global mutex on self.currently_locked, currently no
        // thread can newly call Self::lock() and create a clone of our Arc. Similarly,
        // no other thread can enter Self::unlock() and reduce the strong_count of the Arc.
        // This means that if Arc::strong_count() == 1, we know that we can clean up
        // without race conditions.
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU32, Ordering};
    use std::thread::{self, JoinHandle};
    use std::time::Duration;

    #[test]
    fn simple_lock_unlock() {
        let pool = LockPool::new();
        assert_eq!(0, pool.num_locked());
        let guard = pool.lock(4).unwrap();
        assert_eq!(1, pool.num_locked());
        std::mem::drop(guard);
        assert_eq!(0, pool.num_locked());
    }

    #[test]
    fn simple_try_lock_unlock() {
        let pool = LockPool::new();
        assert_eq!(0, pool.num_locked());
        let guard = pool.try_lock(4).unwrap();
        assert_eq!(1, pool.num_locked());
        std::mem::drop(guard);
        assert_eq!(0, pool.num_locked());
    }

    #[test]
    fn multi_lock_unlock() {
        let pool = LockPool::new();
        assert_eq!(0, pool.num_locked());
        let guard1 = pool.lock(1).unwrap();
        assert_eq!(1, pool.num_locked());
        let guard2 = pool.lock(2).unwrap();
        assert_eq!(2, pool.num_locked());
        let guard3 = pool.lock(3).unwrap();
        assert_eq!(3, pool.num_locked());

        std::mem::drop(guard2);
        assert_eq!(2, pool.num_locked());
        std::mem::drop(guard1);
        assert_eq!(1, pool.num_locked());
        std::mem::drop(guard3);
        assert_eq!(0, pool.num_locked());
    }

    #[test]
    fn multi_try_lock_unlock() {
        let pool = LockPool::new();
        assert_eq!(0, pool.num_locked());
        let guard1 = pool.try_lock(1).unwrap();
        assert_eq!(1, pool.num_locked());
        let guard2 = pool.try_lock(2).unwrap();
        assert_eq!(2, pool.num_locked());
        let guard3 = pool.try_lock(3).unwrap();
        assert_eq!(3, pool.num_locked());

        std::mem::drop(guard2);
        assert_eq!(2, pool.num_locked());
        std::mem::drop(guard1);
        assert_eq!(1, pool.num_locked());
        std::mem::drop(guard3);
        assert_eq!(0, pool.num_locked());
    }

    // Launch a thread that
    // 1. locks the given key
    // 2. once it has the lock, increments a counter
    // 3. then waits until a barrier is released before it releases the lock
    fn launch_locking_thread(
        pool: &Arc<LockPool<isize>>,
        key: isize,
        counter: &Arc<AtomicU32>,
        barrier: Option<&Arc<Mutex<()>>>,
    ) -> JoinHandle<()> {
        let pool = Arc::clone(pool);
        let counter = Arc::clone(counter);
        let barrier = barrier.map(Arc::clone);
        thread::spawn(move || {
            let guard = pool.lock(key);
            counter.fetch_add(1, Ordering::SeqCst);
            let _guard = guard.unwrap();
            if let Some(barrier) = barrier {
                let _barrier = barrier.lock().unwrap();
            }
        })
    }

    #[test]
    fn concurrent_lock() {
        let pool = Arc::new(LockPool::new());
        let guard = pool.lock(5).unwrap();

        let counter = Arc::new(AtomicU32::new(0));

        let child = launch_locking_thread(&pool, 5, &counter, None);

        // Check that even if we wait, the child thread won't get the lock
        thread::sleep(Duration::from_millis(100));
        assert_eq!(0, counter.load(Ordering::SeqCst));

        // Check that we can stil lock other locks while the child is waiting
        {
            let _g = pool.lock(4).unwrap();
        }

        // Now free the lock so the child can get it
        std::mem::drop(guard);

        // And check that the child got it
        child.join().unwrap();
        assert_eq!(1, counter.load(Ordering::SeqCst));

        assert_eq!(0, pool.num_locked());
    }

    #[test]
    fn concurrent_try_lock() {
        let pool = Arc::new(LockPool::new());
        let guard = pool.lock(5).unwrap();

        let error = pool.try_lock(5).unwrap_err();
        assert!(matches!(error, TryLockError::WouldBlock));

        // Check that we can stil lock other locks while the child is waiting
        {
            let _g = pool.try_lock(4).unwrap();
        }

        // Now free the lock so the we can get it again
        std::mem::drop(guard);

        // And check that we can get it again
        {
            let _g = pool.try_lock(5).unwrap();
        }

        assert_eq!(0, pool.num_locked());
    }

    #[test]
    fn multi_concurrent_lock() {
        let pool = Arc::new(LockPool::new());
        let guard = pool.lock(5).unwrap();

        let counter = Arc::new(AtomicU32::new(0));
        let barrier = Arc::new(Mutex::new(()));
        let barrier_guard = barrier.lock().unwrap();

        let child1 = launch_locking_thread(&pool, 5, &counter, Some(&barrier));
        let child2 = launch_locking_thread(&pool, 5, &counter, Some(&barrier));

        // Check that even if we wait, the child thread won't get the lock
        thread::sleep(Duration::from_millis(100));
        assert_eq!(0, counter.load(Ordering::SeqCst));

        // Check that we can stil lock other locks while the children are waiting
        {
            let _g = pool.lock(4).unwrap();
        }

        // Now free the lock so a child can get it
        std::mem::drop(guard);

        // Check that a child got it
        thread::sleep(Duration::from_millis(100));
        assert_eq!(1, counter.load(Ordering::SeqCst));

        // Allow the child to free the lock
        std::mem::drop(barrier_guard);

        // Check that the other child got it
        child1.join().unwrap();
        child2.join().unwrap();
        assert_eq!(2, counter.load(Ordering::SeqCst));

        assert_eq!(0, pool.num_locked());
    }
}
