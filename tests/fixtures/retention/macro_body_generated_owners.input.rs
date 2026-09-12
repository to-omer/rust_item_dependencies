macro_rules! value {
    () => {{
        let closure = || 40_usize;
        let values = [0_u8; const { 2 }];
        closure() + values.len()
    }};
}

macro_rules! length {
    () => { [0_u8; const { 2 }].len() };
}

macro_rules! functions {
    () => {
        fn kept() -> usize { value!() }
fn unused() -> usize { value!() }
        struct Values;
        impl Values {
            fn kept() -> usize { value!() }
fn unused() -> usize { value!() }
        }
        fn nested_closure() -> usize { (|| value!())() }
fn unused_closure() -> usize { (|| value!())() }
        fn nested_const() -> usize { const { length!() } }
fn unused_const() -> usize { const { length!() } }
    };
}

functions!();

fn main() {
    let total = kept() + Values::kept() + nested_closure() + nested_const();
    assert_eq!(total, 128);
    println!("{total}");
}
