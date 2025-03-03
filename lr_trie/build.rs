use std::fs::copy;
use std::path::Path;

fn main() {
    cp("res");
    cp("uc")
}

fn cp(load: &str) {
    let src = format!("../{}/src/lib.rs", load);
    let dst = format!("./src/{}/mod.rs", load);

    let src = Path::new(src.as_str());
    let dst = Path::new(dst.as_str());
    _ = copy(src, dst);
}
