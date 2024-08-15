## Plain Trie

Plain trie is basic trie that allows mapping of any T to string composed of English alphabet letters.

```rust
let key = Key::new("touchstone").unwrap();

let mut trie = Trie::new();
trie.insert(3usize, &key);

assert!(trie.member(&key).is_some());
```
