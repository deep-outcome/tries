### POETRIE

Poetrie means poetic trie. Poetrie is designated for searching common suffixes of words.

#### Basic Usage

##### classic use case

```rust
let mut poetrie = Poetrie::new();
let words = ["analytics", "metrics", "ethics", "Acoustics"]
    .map(|x| Entry::new_from_str(x).unwrap());
for w in words {
    poetrie.ins(&w);
}

let probe = Entry::new_from_str("lyrics").unwrap();
let matchee = poetrie.suf(&probe);
assert_eq!(Ok(String::from("metrics")), matchee);

let probe = Entry::new_from_str("solemn").unwrap();
assert_eq!(Err(FindErr::NoJointSuffix), poetrie.suf(&probe));
```

##### handy use case

Thinking about what could be good rhyming with word of choice, simple try search for that suffix directly. Let say, having _"lyrics"_ as word without match, thinking it should rhyme with something ending with _"ynx"_. 

```rust
let mut poetrie = Poetrie::new();
let words = ["lynx", "index"].map(|x| Entry::new_from_str(x).unwrap());
for w in words {
    poetrie.ins(&w);
}

let probe = Entry::new_from_str("ynx").unwrap();
let matchee = poetrie.suf(&probe);
assert_eq!(Ok(String::from("lynx")), matchee);
```

Now, one goes: _"As the paws in a snow, </br>
lain down by lightening lynx, </br>
my word goes there and forth, </br>
composing the aerial lyrics."_.
