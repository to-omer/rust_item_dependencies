mod origin {
    pub struct Value;
    pub struct GlobValue;
    pub struct Unused;

    impl Value {
        pub fn inherent(&self) -> u8 {
            0
        }
    }

    pub trait Action {
        fn act(&self) -> u8;

        fn static_value() -> u8 {
            1
        }
    }

    impl Action for Value {
        fn act(&self) -> u8 {
            1
        }
    }
}

mod facade {
    pub use crate::origin::{
        Action as ExportedAction, Unused as UnusedExport, Value as ExportedValue,
    };
}

mod explicit_case {
    use crate::facade as f;
    use f::{
        ExportedAction as _, ExportedValue as ValueAlias, UnusedExport as UnusedAlias,
    };

    pub fn run() -> u8 {
        let _: Option<ValueAlias> = None;
        let value = ValueAlias;
        let first = value.act();
        let second = value.act();
        let third = ValueAlias::static_value();
        let inherent = value.inherent();
        match value {
            ValueAlias => first + second + third + inherent,
        }
    }
}

mod glob_facade {
    pub use crate::origin::*;
}

mod glob_case {
    use crate::glob_facade::*;

    pub fn run() {
        let _: Option<GlobValue> = None;
    }
}

mod primitive_case {
    use std::u8;

    pub fn run() -> u8 {
        u8::max_value()
    }
}

#[allow(deprecated)]
mod primitive_module_case {
    use std::u8;

    pub fn run() -> u8 {
        u8::MAX
    }
}

fn main() {
    let _ = explicit_case::run();
    glob_case::run();
    let _ = primitive_case::run();
    let _ = primitive_module_case::run();
}
