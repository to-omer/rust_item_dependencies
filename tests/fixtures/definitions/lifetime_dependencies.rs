struct Hold<'a>(&'a u8);

fn borrow<'a>(value: &'a u8) -> &'a u8 {
    value
}

fn main() {}
