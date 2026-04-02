## POETRIE

Poetrie means poetic trie. Poetrie is designated for searching common suffixes of words.

### Usage

<h4><u>Classic Use Case</u></h4>

Note configuration to match behavior communicated via `MatchConduct` structure.

```rust
let mut poetrie = Poetrie::nw();
let words = [
    "analytics",
    "metrics",
    "ethics",
    "Acoustics",
    "antics",
    "topics",
    "anticruelty",
]
.map(Entry::new_from_str)
.map(Option::unwrap);

for w in words {
    poetrie.it(&w);
}

let mc = MatchConductShaper::init()
    .max_n(usize::MAX) // unlimited matches count
    .max_sl(3) // only 'ics' or less but not '…rics'
    .max_ml(8) // only 8 or less length matches
    .sculpt()
    .unwrap();

let probe = Entry::new_from_str("lyrics").unwrap();
let matchee = poetrie.sx(&probe, &mc);

let confirmation: HashSet<String> =
    ["ethics", "antics", "topics"].map(String::from).into();

let matchee = matchee.unwrap_or_default();
for m in matchee.iter() {
    assert!(confirmation.contains(m));
}
assert_eq!(confirmation.len(), matchee.len());

let mc = MatchConduct::default();

let probe = Entry::new_from_str("anticruelty").unwrap();
assert_eq!(Err(FindErr::OnlyKeyMatches), poetrie.sx(&probe, &mc));

let probe = Entry::new_from_str("solemn").unwrap();
assert_eq!(Err(FindErr::NoJointSuffix), poetrie.sx(&probe, &mc));
```

<h4><u>Handy Use Case</u></h4>

Thinking about what could be good rhyming with word of choice, simple try search for that suffix directly. Let say, having _"lyrics"_ as word without match, thinking it should rhyme with something ending with _"ynx"_. 

```rust
let mut poetrie = Poetrie::nw();
let words = ["lynx", "index"].map(Entry::new_from_str).map(Option::unwrap);

for w in words {
    poetrie.it(&w);
}

let probe = Entry::new_from_str("ynx").unwrap();
let mc = MatchConduct::default();
let matchee = poetrie.sx(&probe, &mc);

assert_eq!(Ok(vec![String::from("lynx")]), matchee);
```

Now, one goes: _"As the paws in a snow, </br>
laid down by lightening lynx, </br>
my word goes there and forth, </br>
composing the aerial lyrics."_.
