#[cfg(all(ONLINE_JUDGE, r#fn, not(debug_assertions)))]
fn value() -> u32 {
    7
}

#[cfg(not(all(ONLINE_JUDGE, r#fn, not(debug_assertions))))]
fn value() -> u32 {
    11
}

fn unused() -> u32 {
    99
}

fn main() {
    println!("{}", value());
}
