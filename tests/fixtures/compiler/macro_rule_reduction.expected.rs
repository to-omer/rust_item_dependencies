#[macro_export]
macro_rules! _dispatch {
    () => {
        _dispatch!(@emit);
    };
    (@emit) => {
        fn value() -> u32 {
            7
        }
    };
    
}

macro_rules! _shift {
    
    () => {
        fn shifted() -> u32 {
            11
        }
    };
}

macro_rules! forward {
    ($item:item) => {
        $item
    };
}

forward! {
    macro_rules! generated {
        () => {
            fn forwarded() -> u32 {
                13
            }
        };
    }
}

_dispatch!();
_shift!();
generated!();

fn main() {
    assert_eq!(value() + shifted() + forwarded(), 31);
}
