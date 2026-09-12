mod values {
    use std::assert as required;
use std::debug_assert as unused_check;

    macro_rules! functions {
        () => {
            pub fn kept() -> u32 { required!(true); 42 }
fn unused() { unused_check!(false); }
        };
    }
    functions!();
}

fn main() {
    assert_eq!(values::kept(), 42);
    println!("{}", values::kept());
}
