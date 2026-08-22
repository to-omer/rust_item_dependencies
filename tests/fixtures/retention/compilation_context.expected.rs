#[cfg(all(ONLINE_JUDGE, r#fn, not(debug_assertions)))]
fn value() -> u32 {
    7
}





fn main() {
    println!("{}", value());
}
