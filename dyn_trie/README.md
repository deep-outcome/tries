## Dynamic Trie

Dynamic trie is trie that allows mapping of any T to any char iterator with asymptotical computational complexity based on that of `std::collections::HashMap`.

Node occurs for each `char` as defined by Rust language.

```rust
let mut trie = Trie::<char>::new();

let some = "información meteorológica".chars();
trie.ins('🌩', some.clone());

let one_more = "alimentación RSS".chars();
trie.ins('😋', one_more.clone());

assert_eq!(RemRes::Ok('😋'), trie.rem(one_more.clone()));
assert_eq!(AcqRes::Err(KeyErr::Unknown), trie.acq(one_more.clone()));
assert_eq!(AcqRes::Ok(&'🌩'), trie.acq(some.clone()));
```
