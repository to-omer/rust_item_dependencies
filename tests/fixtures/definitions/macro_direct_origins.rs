macro_rules! make_products {
    () => {
        fn generated() -> impl Copy {
            let _ = async {};
            1_u8
        }
    };
}

make_products!();

fn main() {}
