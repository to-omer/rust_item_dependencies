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

proc_fixture::make_unused!();

#[proc_fixture::passthrough]
fn unused_attributed() -> i32 { 101 }

#[derive(proc_fixture::Answer)]
struct UnusedMarker;

fn unused_outside() -> i32 { 100 }

fn main() {
    println!("{}", retained::value() + Marker::answer() + proc_fixture::one!());
}
