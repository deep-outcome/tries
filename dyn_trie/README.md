## Dynamic Trie

Dynamic trie is trie that allows mapping of any T to any char iterator with asymptotical computational complexity based on that of `std::collections::HashMap`.

Node occurs for each `char` as defined by Rust language.

```rust
let mut trie = Trie::<char>::new();

let some = "información meteorológica".chars();
trie.insert('🌩', some.clone());

let one_more = "alimentación RSS".chars();
trie.insert('😋', one_more.clone());

assert!(trie.delete(one_more.clone()).is_ok());
assert!(trie.member(one_more.clone()).is_none());
assert_eq!(Some(&'🌩'), trie.member(some.clone()));
```
