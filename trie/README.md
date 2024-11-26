## (plain) trie

- plain trie is classic retrieval tree implementation with fixed size alphabet per node
- allows to use any `impl Iterator<Item = char>` type as key
- oob support for English small letters only
- all methods with classic trie asymptotic computational complexity
- customizable alphabet support

### basic usage

```rust
let mut trie = Trie::new();
let key = || "oomph".chars();
let val = 333;

_ = trie.ins(key(), val);
match trie.acq(key()) {
    AcqRes::Ok(v) => assert_eq!(&val, v),
    _ => panic!("Expected AcqRes::Ok(_).")
}

let val = 444;
_ = trie.ins(key(), val);
match trie.acq(key()) {
    AcqRes::Ok(v) => assert_eq!(&val, v),
    _ => panic!("Expected AcqRes::Ok(_).")
}

let catch = catch_unwind(move|| _ = trie.ins("A".chars(), 0));
assert!(catch.is_err());
```

### custom alphabet implementation

- use `Trie::new_with` in conjunction with implementation for _"ab"_ and _"ix"_ fucntions
- example bellow shows sample implementation for alphabet extended with capital letters


```rust
use plain_trie::{ab as ab_fn, AcqRes, Alphabet, RemRes, Trie};

const ALPHABET_LEN: u32 = 52;

fn ix(c: char) -> usize {
    let big_a = u32::from('A');
    let big_z = u32::from('Z');

    let sma_a = u32::from('a');
    let sma_z = u32::from('z');

    let cod_poi = u32::from(c);
    (match cod_poi {
        c if c >= big_a && c <= big_z => c - big_a,
        c if c >= sma_a && c <= sma_z => c - sma_a + ALPHABET_LEN / 2,
        _ => {
            panic!("Index conversion impossible.")
        }
    }) as usize
}

fn ab() -> Alphabet<usize> {
    ab_fn(ALPHABET_LEN as usize)
}

#[test]
fn test() {
    let mut trie = Trie::new_with(ix, ab);

    let kv_1 = ("AZ", 1);
    let kv_2 = ("az", 2);

    for kv in [kv_1, kv_2] {
        let res = trie.ins(kv.0.chars(), kv.1);
        assert_eq!(true, res.is_ok());
    }

    for kv in [kv_1, kv_2] {
        let res = trie.acq(kv.0.chars());
        assert_eq!(AcqRes::Ok(&kv.1), res);
    }

    for kv in [kv_1, kv_2] {
        let res = trie.rem(kv.0.chars());
        assert_eq!(RemRes::Ok(kv.1), res);
    }
}
```
