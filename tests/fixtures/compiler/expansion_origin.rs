macro_rules! make_items {
    () => {
        fn generated_one() {}
        fn generated_two() {}
    };
}

make_items!();

macro_rules! inner {
    () => {
        fn nested_generated() {}
    };
}

macro_rules! outer {
    () => {
        inner!();
    };
}

outer!();

macro_rules! forwarded {
    () => {
        fn forwarded_generated() {}
    };
}

macro_rules! forward {
    ($($tokens:tt)*) => {
        $($tokens)*
    };
}

forward!(forwarded!(););

macro_rules! define_late {
    () => {
        macro_rules! late {
            () => {
                "late"
            };
        }
    };
}

define_late!();

const RETRY: &str = concat!(late!());
const EAGER: &str = concat!("line=", line!());

#[derive(Clone)]
struct Derived;

#[test]
fn test_only() {}

fn main() {
    println!("expansion-origin");
    generated_one();
    nested_generated();
    forwarded_generated();
    let _ = (RETRY, EAGER);
    let _ = Derived.clone();
}
