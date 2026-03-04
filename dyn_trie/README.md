## Dynamic Trie

Dynamic trie is trie that allows mapping of any T to any char iterator with asymptotical computational complexity based on that of `std::collections::HashMap`.

Node occurs for each `char` as defined by Rust language.

```rust
use dyn_trie::{KeyErr, Trie};

let mut trie = Trie::<char>::new();

let some = "información meteorológica".chars();
_ = trie.ins('🌩', some.clone());

let one_more = "alimentación RSS".chars();
_ = trie.ins('😋', one_more.clone());

assert_eq!(Ok('😋'), trie.rem(one_more.clone()));
assert_eq!(Err(KeyErr::Unknown), trie.acq(one_more.clone()));

let res = trie.acq_mut(some.clone());
assert_eq!(Ok(&mut '🌩'), res);
let entry = res.unwrap();
*entry = '🌞';

assert_eq!(Ok(&'🌞'), trie.acq(some.clone()));
```

```rust
use dyn_trie::{InsResAide, Trie};

let mut trie = Trie::new();
let key = || "abc".chars();

let test = trie.ins(3, key());
assert!(!test.previous());

let mut test = trie.ins(4, key());
assert_eq!(3, test.uproot_previous());
```
