#![allow(dead_code)]

macro_rules! direct {
    () => {
        fn direct_generated() {}
    };
}

direct!();

macro_rules! nested {
    () => {
        fn nested_generated() {}
    };
}

macro_rules! outer {
    () => {
        nested!();
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

const EAGER: &str = concat!(late!());

#[derive(Clone)]
struct Derived;

fn main() {
    direct_generated();
    nested_generated();
    forwarded_generated();
    let _ = EAGER;
    let _ = Derived.clone();
}
