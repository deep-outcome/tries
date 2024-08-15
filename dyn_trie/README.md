## Dynamic Trie

Dynamic trie is trie that allows mapping of any T to any string with complexity based on hash map complexity.

```rust
let mut trie = Trie::new();

let keyword = Key::new("Keyword").unwrap();
trie.insert(0usize, &keyword);

let key = Key::new("Key").unwrap();
trie.insert(0usize, &key);

assert!(trie.delete(&key).is_ok());
assert!(trie.member(&key).is_none());
```
