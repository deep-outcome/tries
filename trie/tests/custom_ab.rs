use plain_trie::{RemRes, Trie};

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

#[test]
fn custom_ab() {
    let mut trie = Trie::new_with(ix, None, ALPHABET_LEN as usize);

    let kv_1 = ("AZ", 1);
    let kv_2 = ("az", 2);

    for kv in [kv_1, kv_2] {
        let res = trie.ins(kv.0.chars(), kv.1);
        assert_eq!(true, res.is_ok());
    }

    for kv in [kv_1, kv_2] {
        let res = trie.acq(kv.0.chars());
        assert_eq!(Ok(&kv.1), res);
    }

    for kv in [kv_1, kv_2] {
        let res = trie.rem(kv.0.chars());
        assert_eq!(RemRes::Ok(kv.1), res);
    }
}
