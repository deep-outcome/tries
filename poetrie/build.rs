use std::fs::copy;
use std::path::Path;

fn main() {
    support("uc");
    support("aide");
}

fn support(supp: &str) {
    let dir = format!("./src/{}", supp);
    _ = std::fs::create_dir(dir);

    let src = format!("../../rust-helpers/src/{}.rs", supp);
    let dst = format!("./src/{}/mod.rs", supp);

    let src = Path::new(src.as_str());
    let dst = Path::new(dst.as_str());
    _ = copy(src, dst);
}
