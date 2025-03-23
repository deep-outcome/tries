## Left-Right Trie

Left-Right trie is trie that allows mapping of any string to any string with complexity based on alphabet used size.

```rust
const ONE: &str = "emoción";
const ANOTHER: &str = "emotion";
const REPLACEMENT: &str = "equilibrio sicofísico";

let mut trie = LrTrie::new();

let one = &KeyEntry::new(ONE).unwrap();
let another = &KeyEntry::new(ANOTHER).unwrap();
let replacement = &KeyEntry::new(REPLACEMENT).unwrap();

trie.insert(one, another);
assert!(trie.member(one, LeftRight::Left).is_some());
assert!(trie.member(another, LeftRight::Left).is_none());
assert!(trie.member(another, LeftRight::Right).is_some());

trie.insert(one, replacement);
assert_eq!(
    Some(String::from(REPLACEMENT)),
    trie.member(&one, LeftRight::Left)
);
assert!(trie.member(another, LeftRight::Right).is_none());
assert_eq!(
    Some(String::from(ONE)),
    trie.member(replacement, LeftRight::Right)
);

assert_eq!(Ok(()), trie.delete(one, LeftRight::Left));

assert!(trie.member(one, LeftRight::Left).is_none());
assert!(trie.member(replacement, LeftRight::Right).is_none());

assert_eq!(Err(()), trie.delete(replacement, LeftRight::Right));
```
