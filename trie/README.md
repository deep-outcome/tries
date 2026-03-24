## (plain) trie

- plain trie is classic retrieval tree implementation with fixed size alphabet per node
- allows to use any `impl Iterator<Item = char>` type as key
- oob support for English small letters only
- all methods with classic trie asymptotic computational complexity
- customizable alphabet support

### basic usage

```rust
use plain_trie::Trie;
use std::panic::catch_unwind;

let mut trie = Trie::new();
let key = || "oomph".chars();
let val = 333;

_ = trie.ins(key(), val);
match trie.acq(key()) {
    Ok(v) => assert_eq!(&val, v),
    _ => panic!("Expected Ok(_).")
}

let val = 444;
_ = trie.ins(key(), val);
match trie.acq(key()) {
    Ok(v) => assert_eq!(&val, v),
    _ => panic!("Expected Ok(_).")
}

let catch = catch_unwind(move|| _ = trie.ins("A".chars(), 0));
assert!(catch.is_err());
```

```rust
use plain_trie::{InsResAide, Trie};

let mut trie = Trie::new();
let key = || "abc".chars();

let test = trie.ins(key(), 3);
assert!(!test.previous());

let mut test = trie.ins(key(), 4);
assert_eq!(3, test.uproot_previous());
```

### custom alphabet implementation

- use `Trie::new_with` in conjunction with implementation for char-index conversion functions and apposite alphabet length
- example bellow shows sample implementation for alphabet extended with capital letters


```rust
use plain_trie::Trie;

const ALPHABET_LEN: usize = 52;
const ALPHABET_HALFLEN: usize = ALPHABET_LEN / 2;

fn ix(c: char) -> usize {
    let big_a = u32::from('A');
    let big_z = u32::from('Z');

    let sma_a = u32::from('a');
    let sma_z = u32::from('z');

    let code_point = u32::from(c);
    let ix = match code_point {
        c if c >= big_a && c <= big_z => c - big_a,
        c if c >= sma_a && c <= sma_z => c - sma_a + ALPHABET_HALFLEN as u32,
        _ => {
            panic!("Index conversion impossible.")
        }
    };

    ix as usize
}

fn re(ix: usize) -> char {
    let big_a = u32::from('A') as usize;
    let sma_a = u32::from('a') as usize;

    let code_point = if ix < ALPHABET_HALFLEN {
        ix + big_a
    } else {
        ix + sma_a - ALPHABET_HALFLEN
    } as u8;

    code_point as char
}

#[test]
fn test() {
    let mut trie = Trie::new_with(ix, re, ALPHABET_LEN);

    let keyvals = vec![(String::from("AZ"), &1), (String::from("az"), &2)];

    for kv in keyvals.iter() {
        let res = trie.ins(kv.0.chars(), *kv.1);
        assert_eq!(true, res.is_ok());
    }

    for kv in keyvals.iter() {
        let res = trie.acq(kv.0.chars());
        assert_eq!(Ok(kv.1), res);
    }

    let view = trie.view().unwrap();
    assert_eq!(keyvals, view);

    for kv in keyvals.iter() {
        let res = trie.rem(kv.0.chars());
        assert_eq!(Ok(*kv.1), res);
    }
}
```
