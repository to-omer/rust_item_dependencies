macro_rules! nested_items {
    ($( $module:ident => [$( $name:ident => $value:expr),*]);*) => {
        $(
            pub mod $module {
                pub struct Anchor;
                $(
                    pub struct $name;

                    impl $name {
                        pub fn value() -> u32 {
                            $value
                        }
                    }
                )*
            }
        )*
    };
}

nested_items!(
    first => [kept => 7, partially_kept => 8];
    emptied => []
);

macro_rules! emit_one {
    ($name:ident => $value:expr) => {
        pub fn $name() -> u32 {
            $value
        }
    };
}

macro_rules! emit_all {
    ($name:ident => $value:expr $(, $rest_name:ident => $rest_value:expr)*) => {
        emit_one!($name => $value);
        emit_all!($($rest_name => $rest_value),*);
    };
    () => {};
}

mod recursive_first {
    emit_all!(kept => 11);
}

mod recursive_second {
    emit_all!(dead => 13, kept => 14);
}

macro_rules! emit_with_terminator {
    ($name:ident => $value:expr $(, $rest_name:ident => $rest_value:expr)*) => {
        pub fn $name() -> u32 {
            $value
        }
        emit_with_terminator!($($rest_name => $rest_value),*);
    };
    () => {
        pub const TERMINATOR: u32 = 5;
    };
}

mod outputful_base {
    emit_with_terminator!(kept => 15, dead => 16);
}

fn main() {
    let _ = first::Anchor;
    let _ = first::partially_kept;
    let _ = emptied::Anchor;
    assert_eq!(first::kept::value(), 7);
    assert_eq!(recursive_first::kept() + recursive_second::kept(), 25);
    assert_eq!(outputful_base::kept() + outputful_base::TERMINATOR, 20);
}
