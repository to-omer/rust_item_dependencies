mod values {
    use std::assert as required;


    macro_rules! functions {
        () => {
            pub fn kept() -> u32 { required!(true); 42 }

        };
    }
    functions!();
}

fn main() {
    assert_eq!(values::kept(), 42);
    println!("{}", values::kept());
}
