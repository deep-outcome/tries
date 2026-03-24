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
fn custom_ab() {
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
