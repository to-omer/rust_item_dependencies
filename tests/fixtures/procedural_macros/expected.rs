#[cfg_attr(all(), proc_fixture::passthrough)]
mod retained {
    macro_rules! choose {
        () => { 40 };
        ($value:expr) => { $value };
    }

    pub fn value() -> i32 { choose!() }

    fn unused_nested() -> i32 { 99 }
}

#[derive(Clone)]
#[derive(proc_fixture::Answer)]
struct Marker;

#[derive(proc_fixture::Answer)]
#[derive(Clone)]
struct ReverseMarker;









fn main() {
    let _ = ReverseMarker.clone();
    println!("{}", retained::value() + Marker::answer() + proc_fixture::one!());
}
