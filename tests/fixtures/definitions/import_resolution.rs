mod definitions {
    pub fn direct() {}

    pub mod nested {
        pub fn renamed() {}
        pub fn globbed() {}
    }

    pub trait Speak {
        fn speak(&self);
    }

    impl Speak for u8 {
        fn speak(&self) {}
    }
}

use crate::definitions::{
    direct as alias,
    nested::{renamed as nested_alias, *},
    Speak as _,
};

fn main() {
    alias();
    nested_alias();
    globbed();
    1_u8.speak();
}
