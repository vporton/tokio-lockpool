use owning_ref::OwningHandle;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::{Arc, Mutex, MutexGuard};

use super::{Guard, PoisonError, TryLockError, UnpoisonError};

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
/// # (|| -> Result<(), lockpool::PoisonError<_, _>> {
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
    ///
    /// Corner case: Poisoned locks count as locked even if they're currently not locked
    pub fn num_locked_or_poisoned(&self) -> usize {
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
    /// # (|| -> Result<(), lockpool::PoisonError<_, _>> {
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
    pub fn lock(&self, key: K) -> Result<Guard<'_, K>, PoisonError<K, Guard<'_, K>>> {
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
    /// - If another user of this lock panicked while holding the lock, then this call will return [TryLockError::Poisoned].
    /// - If the lock could not be acquired because it is already locked, then this call will return [TryLockError::WouldBlock].
    ///
    /// Examples
    /// -----
    /// ```
    /// use lockpool::{TryLockError, LockPool};
    ///
    /// let pool = LockPool::new();
    /// # (|| -> Result<(), lockpool::PoisonError<_, _>> {
    /// let guard1 = pool.lock(4)?;
    /// let guard2 = pool.lock(5)?;
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
    pub fn try_lock(&self, key: K) -> Result<Guard<'_, K>, TryLockError<K, Guard<'_, K>>> {
        let mutex = self._load_or_insert_mutex_for_key(&key);
        self._try_lock(key, mutex)
    }

    /// Unpoisons a poisoned lock.
    ///
    /// Generally, once a thread panics while a lock is held, that lock is poisoned forever and all future attempts at locking it will return a [PoisonError].
    /// This is since the resources protected by the lock are likely in an invalid state if the thread panicked while having the lock.
    ///
    /// However, if you need an escape hatch, this function is it. Using it, you can unpoison a lock so that it can be locked again.
    /// This only works if currently no other thread is waiting for the lock.
    ///
    /// Errors:
    /// -----
    /// - Returns [UnpoisonError::NotPoisoned] if the lock wasn't actually poisoned
    /// - Returns [UnpoisonError::OtherThreadsBlockedOnMutex] if there are other threads currently waiting for this lock
    pub fn unpoison(&self, key: K) -> Result<(), UnpoisonError> {
        let mut currently_locked = self._currently_locked();
        let mutex: &Arc<Mutex<()>> = currently_locked
            .get(&key)
            .ok_or(UnpoisonError::NotPoisoned)?;
        if Arc::strong_count(mutex) != 1 {
            return Err(UnpoisonError::OtherThreadsBlockedOnMutex);
        }
        let result = match Arc::clone(mutex).lock() {
            Ok(_) => Err(UnpoisonError::NotPoisoned),
            Err(_) => {
                // If we're here, then we know that the mutex is in fact poisoned and there's no other threads having access to the mutex at the moment.
                // Thanks to the global lock on currently_locked, we know that no other thread can get access to it either at the moment.
                // The best way to unpoison the mutex is to just remove it. It will be recreated the next time somebody asks for it.
                let remove_result = currently_locked.remove(&key);
                assert!(
                    remove_result.is_some(),
                    "We just got this entry above from the hash map, it cannot have vanished since then"
                );
                Ok(())
            }
        };
        result
    }

    fn _currently_locked(&self) -> MutexGuard<'_, HashMap<K, Arc<Mutex<()>>>> {
        self.currently_locked
            .lock()
            .expect("The global mutex protecting the lock pool is poisoned. This shouldn't happen since there shouldn't be any user code running while this lock is held so no thread should ever panic with it")
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
    ) -> Result<Guard<'_, K>, PoisonError<K, Guard<'_, K>>> {
        let mut poisoned = false;
        let guard = OwningHandle::new_with_fn(mutex, |mutex: *const Mutex<()>| {
            let mutex: &Mutex<()> = unsafe { &*mutex };
            match mutex.lock() {
                Ok(guard) => guard,
                Err(poison_error) => {
                    poisoned = true;
                    poison_error.into_inner()
                }
            }
        });
        if poisoned {
            let guard = Guard::new(self, key.clone(), guard, true);
            Err(PoisonError::LockPoisoned { key, guard })
        } else {
            let guard = Guard::new(self, key, guard, false);
            Ok(guard)
        }
    }

    fn _try_lock(
        &self,
        key: K,
        mutex: Arc<Mutex<()>>,
    ) -> Result<Guard<'_, K>, TryLockError<K, Guard<'_, K>>> {
        let mut poisoned = false;
        let guard = OwningHandle::try_new(mutex, |mutex: *const Mutex<()>| {
            let mutex: &Mutex<()> = unsafe { &*mutex };
            match mutex.try_lock() {
                Ok(guard) => Ok(guard),
                Err(std::sync::TryLockError::Poisoned(poison_error)) => {
                    poisoned = true;
                    Ok(poison_error.into_inner())
                }
                Err(std::sync::TryLockError::WouldBlock) => Err(TryLockError::WouldBlock),
            }
        })?;
        if poisoned {
            let guard = Guard::new(self, key.clone(), guard, true);
            Err(TryLockError::Poisoned(PoisonError::LockPoisoned {
                key,
                guard,
            }))
        } else {
            let guard = Guard::new(self, key, guard, false);
            Ok(guard)
        }
    }

    pub(super) fn _unlock(
        &self,
        key: &K,
        guard: OwningHandle<Arc<Mutex<()>>, MutexGuard<'_, ()>>,
        poisoned: bool,
    ) {
        if poisoned {
            // If the guard is poisoned, then we still unlock the lock but this happens by dropping
            // the guard. We keep poisoned locks in the hashmap.
            return;
        }

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

        if Arc::strong_count(mutex) == 1 && !std::thread::panicking() {
            // The guard we're about to drop is the last guard for this mutex,
            // the only other Arc pointing to it is the one in the hashmap.
            // We can clean up
            // We don't clean up if we're panicking because we want to keep the
            // lock poisoned in this case.
            let remove_result = currently_locked.remove(key);
            assert!(
                remove_result.is_some(),
                "We just got this entry above from the hash map, it cannot have vanished since then"
            );
        }
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
        assert_eq!(0, pool.num_locked_or_poisoned());
        let guard = pool.lock(4).unwrap();
        assert_eq!(1, pool.num_locked_or_poisoned());
        std::mem::drop(guard);
        assert_eq!(0, pool.num_locked_or_poisoned());
    }

    #[test]
    fn simple_try_lock_unlock() {
        let pool = LockPool::new();
        assert_eq!(0, pool.num_locked_or_poisoned());
        let guard = pool.try_lock(4).unwrap();
        assert_eq!(1, pool.num_locked_or_poisoned());
        std::mem::drop(guard);
        assert_eq!(0, pool.num_locked_or_poisoned());
    }

    #[test]
    fn multi_lock_unlock() {
        let pool = LockPool::new();
        assert_eq!(0, pool.num_locked_or_poisoned());
        let guard1 = pool.lock(1).unwrap();
        assert_eq!(1, pool.num_locked_or_poisoned());
        let guard2 = pool.lock(2).unwrap();
        assert_eq!(2, pool.num_locked_or_poisoned());
        let guard3 = pool.lock(3).unwrap();
        assert_eq!(3, pool.num_locked_or_poisoned());

        std::mem::drop(guard2);
        assert_eq!(2, pool.num_locked_or_poisoned());
        std::mem::drop(guard1);
        assert_eq!(1, pool.num_locked_or_poisoned());
        std::mem::drop(guard3);
        assert_eq!(0, pool.num_locked_or_poisoned());
    }

    #[test]
    fn multi_try_lock_unlock() {
        let pool = LockPool::new();
        assert_eq!(0, pool.num_locked_or_poisoned());
        let guard1 = pool.try_lock(1).unwrap();
        assert_eq!(1, pool.num_locked_or_poisoned());
        let guard2 = pool.try_lock(2).unwrap();
        assert_eq!(2, pool.num_locked_or_poisoned());
        let guard3 = pool.try_lock(3).unwrap();
        assert_eq!(3, pool.num_locked_or_poisoned());

        std::mem::drop(guard2);
        assert_eq!(2, pool.num_locked_or_poisoned());
        std::mem::drop(guard1);
        assert_eq!(1, pool.num_locked_or_poisoned());
        std::mem::drop(guard3);
        assert_eq!(0, pool.num_locked_or_poisoned());
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

    fn poison_lock(pool: &Arc<LockPool<isize>>, key: isize) {
        let pool_ref = Arc::clone(pool);
        thread::spawn(move || {
            let _guard = pool_ref.lock(key);
            panic!("let's poison the lock");
        })
        .join()
        .expect_err("The child thread should return an error");
    }

    fn poison_try_lock(pool: &Arc<LockPool<isize>>, key: isize) {
        let pool_ref = Arc::clone(pool);
        thread::spawn(move || {
            let _guard = pool_ref.try_lock(key).unwrap();
            panic!("let's poison the lock");
        })
        .join()
        .expect_err("The child thread should return an error");
    }

    fn assert_is_lock_poisoned_error(
        expected_key: isize,
        error: &PoisonError<isize, Guard<'_, isize>>,
    ) {
        match error {
            PoisonError::LockPoisoned {
                key: actual_key, ..
            } => {
                assert_eq!(expected_key, *actual_key);
            }
        }
    }

    fn assert_is_try_lock_poisoned_error(
        expected_key: isize,
        error: &TryLockError<isize, Guard<'_, isize>>,
    ) {
        match error {
            TryLockError::Poisoned(PoisonError::LockPoisoned {
                key: actual_key, ..
            }) => {
                assert_eq!(expected_key, *actual_key);
            }
            _ => panic!("Wrong error type"),
        }
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

        assert_eq!(0, pool.num_locked_or_poisoned());
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

        assert_eq!(0, pool.num_locked_or_poisoned());
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

        assert_eq!(0, pool.num_locked_or_poisoned());
    }

    #[test]
    fn pool_mutex_poisoned_by_lock() {
        let pool = Arc::new(LockPool::new());

        poison_lock(&pool, 3);

        // All future lock attempts should error
        {
            let err = pool.lock(3).unwrap_err();
            assert_is_lock_poisoned_error(3, &err);
        }

        {
            let err = pool.try_lock(3).unwrap_err();
            assert_is_try_lock_poisoned_error(3, &err);
        }

        {
            let err = pool.lock(3).unwrap_err();
            assert_is_lock_poisoned_error(3, &err);
        }

        {
            let err = pool.try_lock(3).unwrap_err();
            assert_is_try_lock_poisoned_error(3, &err);
        }
    }

    #[test]
    fn pool_mutex_poisoned_by_try_lock() {
        let pool = Arc::new(LockPool::new());

        poison_try_lock(&pool, 3);

        // All future lock attempts should error
        {
            let err = pool.lock(3).unwrap_err();
            assert_is_lock_poisoned_error(3, &err);
        }

        {
            let err = pool.try_lock(3).unwrap_err();
            assert_is_try_lock_poisoned_error(3, &err);
        }

        {
            let err = pool.lock(3).unwrap_err();
            assert_is_lock_poisoned_error(3, &err);
        }

        {
            let err = pool.try_lock(3).unwrap_err();
            assert_is_try_lock_poisoned_error(3, &err);
        }
    }

    #[test]
    fn poison_error_holds_lock() {
        let pool = Arc::new(LockPool::new());
        poison_lock(&pool, 5);
        let error = pool.lock(5).unwrap_err();
        assert_is_lock_poisoned_error(5, &error);

        let counter = Arc::new(AtomicU32::new(0));

        let child = launch_locking_thread(&pool, 5, &counter, None);

        // Check that even if we wait, the child thread won't get the lock
        thread::sleep(Duration::from_millis(100));
        assert_eq!(0, counter.load(Ordering::SeqCst));

        // Now free the lock so the child can get it
        std::mem::drop(error);

        // And check that the child got it
        child.join().unwrap_err();
        assert_eq!(1, counter.load(Ordering::SeqCst));

        // The poisoned lock is still there
        assert_eq!(1, pool.num_locked_or_poisoned());
    }

    #[test]
    fn poison_error_holds_try_lock() {
        let pool = Arc::new(LockPool::new());
        poison_lock(&pool, 5);
        let error = pool.lock(5).unwrap_err();
        assert_is_lock_poisoned_error(5, &error);

        let err = pool.try_lock(5).unwrap_err();
        assert!(matches!(err, TryLockError::WouldBlock));

        // Now free the lock so the child can get it
        std::mem::drop(error);

        // And check that it is still poisoned
        let err = pool.try_lock(5).unwrap_err();
        assert_is_try_lock_poisoned_error(5, &err);

        // The poisoned lock is still there
        assert_eq!(1, pool.num_locked_or_poisoned());
    }

    #[test]
    fn unpoison() {
        let pool = Arc::new(LockPool::new());

        poison_lock(&pool, 3);

        // Check that it is actually poisoned
        {
            let err = pool.lock(3).unwrap_err();
            assert_is_lock_poisoned_error(3, &err);
        }

        pool.unpoison(3).unwrap();

        // Check that it got unpoisoned
        {
            let _g = pool.lock(3).unwrap();
        }
        {
            let _g = pool.try_lock(3).unwrap();
        }
    }

    #[test]
    fn unpoison_not_poisoned() {
        let pool = Arc::new(LockPool::new());

        let err = pool.unpoison(3).unwrap_err();
        assert_eq!(UnpoisonError::NotPoisoned, err);
    }

    #[test]
    fn unpoison_while_other_thread_waiting() {
        let pool = Arc::new(LockPool::new());

        poison_lock(&pool, 3);

        // Check that it is actually poisoned
        {
            let err = pool.lock(3).unwrap_err();
            assert_is_lock_poisoned_error(3, &err);
        }

        pool.unpoison(3).unwrap();

        // Check that it got unpoisoned
        {
            let _g = pool.lock(3).unwrap();
        }
    }
}
