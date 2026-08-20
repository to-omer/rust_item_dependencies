macro_rules! define_borrow {
    () => {
        fn generated(value: &u8) -> &u8 {
            value
        }
    };
}

define_borrow!();

fn main() {
    let _ = generated(&0);
}
