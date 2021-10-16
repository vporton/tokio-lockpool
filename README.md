[![Build Status](https://github.com/smessmer/lockpool/actions/workflows/ci.yml/badge.svg)](https://github.com/smessmer/lockpool/actions/workflows/ci.yml)
[![Latest Version](https://img.shields.io/crates/v/lockpool.svg)](https://crates.io/crates/lockpool)
[![docs.rs](https://docs.rs/lockpool/badge.svg)](https://docs.rs/lockpool)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](https://github.com/smessmer/lockpool/blob/master/LICENSE-MIT)
[![License](https://img.shields.io/badge/license-APACHE-blue.svg)](https://github.com/smessmer/lockpool/blob/master/LICENSE-APACHE)
[![codecov](https://codecov.io/gh/smessmer/lockpool/branch/master/graph/badge.svg?token=FRSBH7YYA9)](https://codecov.io/gh/smessmer/lockpool)

# lockpool

This library offers a pool of locks where individual locks can be locked/unlocked by key.
It initially considers all keys as "unlocked", but they can be locked
and if a second thread tries to acquire a lock for the same key, they will have to wait.

```rust
use lockpool::LockPool;

let pool = LockPool::new();
let guard1 = pool.lock(4)?;
let guard2 = pool.lock(5)?;

// This next line would cause a deadlock or panic because `4` is already locked on this thread
// let guard3 = pool.lock(4)?;

// After dropping the corresponding guard, we can lock it again
std::mem::drop(guard1);
let guard3 = pool.lock(4)?;
```

You can use an arbitrary type to index locks by, as long as that type implements [PartialEq] + [Eq] + [Hash] + [Clone] + [Debug].

```rust
use lockpool::LockPool;

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct CustomLockKey(u32);

let pool = LockPool::new();
let guard = pool.lock(CustomLockKey(4))?;
```

Under the hood, a [LockPool] is a [HashMap](std::collections::HashMap) of [Mutex](std::sync::Mutex)es, with some logic making sure there aren't any race conditions when accessing the hash map.

License: MIT OR Apache-2.0

[PartialEq]: https://doc.rust-lang.org/std/cmp/trait.PartialEq.html
[Clone]: https://doc.rust-lang.org/std/clone/trait.Clone.html
[Eq]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
[Hash]: https://doc.rust-lang.org/std/hash/macro.Hash.html
[Debug]: https://doc.rust-lang.org/std/fmt/trait.Debug.html
[LockPool]: https://docs.rs/lockpool/latest/lockpool/struct.LockPool.html
