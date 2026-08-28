use std::sync::atomic::{AtomicU32, Ordering};

static CALLS: AtomicU32 = AtomicU32::new(0);

fn bump() -> u32 {
    CALLS.fetch_add(1, Ordering::SeqCst);
    1
}

macro_rules! direct_components {
    () => {{
        macro_rules! live_macro {
            () => {
                40
            };
        }

        use std::{ marker::PhantomData, cmp::Ordering as CmpOrdering};



        let _: PhantomData<u8> = PhantomData;
        let _ = CmpOrdering::Equal;
        let observed = {
            bump();
            1
        };
        let also_observed = {
            bump();
            1
        };
        live_macro!() + observed + also_observed
    }};
}

macro_rules! make_module {
    ($module:ident, $required:ident, $shared:ident) => {
        mod $module {
            pub fn $required() -> u32 {
                3
            }

            pub fn $shared() -> u32 {
                5
            }


        }
    };
}

macro_rules! inner_type {
    () => {
        u32
    };
}

macro_rules! outer_type {
    () => {
        inner_type!()
    };
}

macro_rules! inner_pattern {
    ($value:ident) => {
        Some($value)
    };
}

macro_rules! outer_pattern {
    ($value:ident) => {
        inner_pattern!($value)
    };
}

type Output = outer_type!();

make_module!(first, first_required, first_shared);
make_module!(second, second_required, second_shared);

fn main() {
    assert_eq!(direct_components!(), 42);
    assert_eq!(CALLS.load(Ordering::SeqCst), 2);
    assert_eq!(
        first::first_required() + first::first_shared() + second::second_required(),
        11
    );
    let output: Output = 7;
    assert_eq!(output, 7);
    assert_eq!(match Some(9) { outer_pattern!(value) => value, None => 0 }, 9);
}
