macro_rules! load_resource {
    () => {
        include_str!("secret.txt")
    };
}

fn main() {
    let _ = load_resource!();
}
