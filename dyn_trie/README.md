## Dynamic Trie

Dynamic trie is trie that allows mapping of any T to any string with asymptotical computational complexity based on that of `std::collections::HashMap`.

Node occurs for each `char` in string as defined by Rust language.

```rust
let mut trie = Trie::new();

let keyword = Key::new("Keyword").unwrap();
trie.insert(0usize, &keyword);

let key = Key::new("Key").unwrap();
trie.insert(0usize, &key);

assert!(trie.delete(&key).is_ok());
assert!(trie.member(&key).is_none());
```
