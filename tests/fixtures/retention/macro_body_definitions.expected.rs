macro_rules! direct_value {
    () => {{

        let closure = || 40_usize;
        let values = [0_u8; const { 2 }];
        closure() + values.len()
    }};
}

macro_rules! forwarded_value {
    ($value:expr) => {{

        $value
    }};
}

fn main() {
    let direct = direct_value!();
    let forwarded = forwarded_value!({
        let closure = || 40_usize;
        let values = [0_u8; const { 2 }];
        closure() + values.len()
    });
    assert_eq!(direct + forwarded, 84);
    println!("{}", direct + forwarded);
}
