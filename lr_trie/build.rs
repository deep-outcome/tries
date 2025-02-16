use std::fs::copy;
use std::path::Path;

fn main() {
    let src = Path::new("../res/src/lib.rs");
    let dst = Path::new("./src/res/mod.rs");
    _ = copy(src, dst);
}
