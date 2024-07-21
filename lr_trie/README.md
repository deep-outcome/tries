## Left-Right Trie

Left-Right trie is trie that allows mapping of any string to any string with complexity based on alphabet used size.

```Rust
let mut trie = LrTrie::new();
let one = KeyEntry::new("emoción").unwrap();
let another = KeyEntry::new("emotion").unwrap();

trie.insert(&one, &another);
assert!(trie.member(&one, LeftRight::Left).is_some());
assert!(trie.member(&another, LeftRight::Left).is_none());
```
