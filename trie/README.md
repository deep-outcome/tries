## Plain Trie

- Plain trie is classic retrieval tree implementation with fixed size alphabet per node.
- Support for English alphabet only.
- Capital letters are lowercased.
- All methods with classic trie ACC (asymptotic computational complexity).

```rust
let key = Key::new("touchstone").unwrap();

let mut trie = Trie::new();
trie.insert(3usize, &key);

assert!(trie.member(&key).is_some());
```
