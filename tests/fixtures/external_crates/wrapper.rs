pub use external_leaf::{Measure, Number};

pub fn external_function() -> i32 {
    external_leaf::leaf_value()
}

pub fn external_generic<T>(value: T) -> T
where
    T: std::ops::Add<Output = T> + Copy,
{
    external_leaf::double(value)
}

#[doc(hidden)]
pub fn macro_value(value: i32) -> i32 {
    value + 1
}

#[macro_export]
macro_rules! external_macro {
    ($value:expr) => {
        {
            macro_rules! import_external_leaf {
                () => {
                    extern crate external_leaf as __external_leaf;
                };
            }
            import_external_leaf!();
            $crate::macro_value($value) + __external_leaf::leaf_value()
        }
    };
}

#[macro_export]
macro_rules! external_passthrough {
    ($item:item) => {
        $item
    };
}

#[macro_export]
macro_rules! external_proc_macro_dependency {
    () => {
        extern crate proc_macro;
    };
}
