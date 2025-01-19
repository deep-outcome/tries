## Dynamic Trie

Dynamic trie is trie that allows mapping of any T to any string with asymptotical computational complexity based on that of `std::collections::HashMap`.

Node occurs for each `char` in string as defined by Rust language.

```rust
let mut trie = Trie::<char>::new();

let some = Key("información meteorológica");
trie.insert('🌩', &some);

let one_more = Key("alimentación RSS");
trie.insert('😋', &one_more);

assert!(trie.delete(&one_more).is_ok());
assert!(trie.member(&one_more).is_none());
assert_eq!(Some(&'🌩'), trie.member(&some));
```
