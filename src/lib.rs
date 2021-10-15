use owning_ref::OwningHandle;
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::{Arc, Mutex, MutexGuard};

pub struct LockPool<K>
where
    K: Eq + PartialEq + Hash + Clone,
{
    currently_locked: Mutex<HashMap<K, Arc<Mutex<()>>>>,
}

impl<K> LockPool<K>
where
    K: Eq + PartialEq + Hash + Clone,
{
    pub fn new() -> Self {
        Self {
            currently_locked: Mutex::new(HashMap::new()),
        }
    }

    pub fn num_locked(&self) -> usize {
        self.currently_locked.lock().expect("Poisoned mutex").len()
    }

    pub fn lock<'a>(&'a self, key: K) -> Guard<'a, K> {
        // TODO Return Result instead of expect()
        let mut currently_locked = self.currently_locked.lock().expect("Poisoned mutex");
        if let Some(mutex) = currently_locked.get_mut(&key).map(|a| Arc::clone(a)) {
            // Drop the global lock so other threads can enter this and lock their keys while we're waiting
            std::mem::drop(currently_locked);

            let guard = OwningHandle::new_with_fn(mutex, |mutex: *const Mutex<()>| {
                // TODO Return Result instead of expect()
                let mutex: &Mutex<()> = unsafe { &*mutex };
                mutex.lock().expect("Poisoned mutex")
            });
            Guard::new(&self, key, guard)
        } else {
            let insert_result = currently_locked.insert(key.clone(), Arc::new(Mutex::new(())));
            assert!(
                insert_result.is_none(),
                "We just checked that the entry doesn't exist, why does it exist now?"
            );
            let mutex = currently_locked
                .get_mut(&key)
                .map(|a| Arc::clone(a))
                .expect("We just inserted this");
            let guard = OwningHandle::new_with_fn(mutex, |mutex: *const Mutex<()>| {
                // TODO Return Result instead of expect()
                let mutex: &Mutex<()> = unsafe { &*mutex };
                mutex.lock().expect("Poisoned mutex")
            });
            Guard::new(&self, key, guard)
        }
    }

    fn unlock(&self, key: &K, guard: OwningHandle<Arc<Mutex<()>>, MutexGuard<'_, ()>>) {
        let mut currently_locked = self.currently_locked.lock().expect("Poisoned mutex");
        let mutex: &Arc<Mutex<()>> = currently_locked
            .get(key)
            .expect("This entry must exist if we're about to unlock it");
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

        if Arc::strong_count(mutex) == 1 {
            // The guard we're about to drop is the last guard for this mutex,
            // the only other Arc pointing to it is the one in the hashmap.
            // We can clean up
            let remove_result = currently_locked.remove(key);
            assert!(
                remove_result.is_some(),
                "Tried to cleanup a lock that didn't exist"
            );
        }
    }
}

pub struct Guard<'a, K>
where
    K: Eq + PartialEq + Hash + Clone,
{
    pool: &'a LockPool<K>,
    key: K,
    guard: Option<OwningHandle<Arc<Mutex<()>>, MutexGuard<'a, ()>>>,
}

impl<'a, K> Guard<'a, K>
where
    K: Eq + PartialEq + Hash + Clone,
{
    fn new(
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
    K: Eq + PartialEq + Hash + Clone,
{
    fn drop(&mut self) {
        let guard = self
            .guard
            .take()
            .expect("The self.guard field must always be set unless this was already destructed");
        self.pool.unlock(&self.key, guard);
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
        let guard = pool.lock(4);
        assert_eq!(1, pool.num_locked());
        std::mem::drop(guard);
        assert_eq!(0, pool.num_locked());
    }

    #[test]
    fn multi_lock_unlock() {
        let pool = LockPool::new();
        assert_eq!(0, pool.num_locked());
        let guard1 = pool.lock(1);
        assert_eq!(1, pool.num_locked());
        let guard2 = pool.lock(2);
        assert_eq!(2, pool.num_locked());
        let guard3 = pool.lock(3);
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
        let pool = Arc::clone(&pool);
        let counter = Arc::clone(&counter);
        let barrier = barrier.map(Arc::clone);
        thread::spawn(move || {
            let _guard = pool.lock(key);
            counter.fetch_add(1, Ordering::SeqCst);
            if let Some(barrier) = barrier {
                let _ = barrier.lock().unwrap();
            }
        })
    }

    #[test]
    fn concurrent_lock() {
        let pool = Arc::new(LockPool::new());
        let guard = pool.lock(5);

        let counter = Arc::new(AtomicU32::new(0));

        let child = launch_locking_thread(&pool, 5, &counter, None);

        // Check that even if we wait, the child thread won't get the lock
        thread::sleep(Duration::from_millis(100));
        assert_eq!(0, counter.load(Ordering::SeqCst));

        // Check that we can stil lock other locks while the child is waiting
        pool.lock(4);

        // Now free the lock so the child can get it
        std::mem::drop(guard);

        // And check that the child got it
        child.join().unwrap();
        assert_eq!(1, counter.load(Ordering::SeqCst));

        assert_eq!(0, pool.num_locked());
    }

    #[test]
    fn multi_concurrent_lock() {
        let pool = Arc::new(LockPool::new());
        let guard = pool.lock(5);

        let counter = Arc::new(AtomicU32::new(0));
        let barrier = Arc::new(Mutex::new(()));
        let barrier_guard = barrier.lock().unwrap();

        let child1 = launch_locking_thread(&pool, 5, &counter, Some(&barrier));
        let child2 = launch_locking_thread(&pool, 5, &counter, Some(&barrier));

        // Check that even if we wait, the child thread won't get the lock
        thread::sleep(Duration::from_millis(100));
        assert_eq!(0, counter.load(Ordering::SeqCst));

        // Check that we can stil lock other locks while the children are waiting
        pool.lock(4);

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
