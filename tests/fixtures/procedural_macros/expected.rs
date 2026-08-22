#[cfg_attr(all(), proc_fixture::passthrough)]
mod retained {
    macro_rules! choose {
        () => { 40 };
        ($value:expr) => { $value };
    }

    pub fn value() -> i32 { choose!() }

    fn unused_nested() -> i32 { 99 }
}

#[derive(proc_fixture::Answer)]
struct Marker;









fn main() {
    println!("{}", retained::value() + Marker::answer() + proc_fixture::one!());
}
