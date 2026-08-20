struct Pair(u8);

fn chosen() -> u8 {
    1
}

fn main() {
    let chosen = || 2_u8;
    let _ = chosen();
    let _ = crate::chosen();

    let Pair(value) = Pair(3);
    let _: Pair;
    let _: Option<u8> = Some(value);
}
