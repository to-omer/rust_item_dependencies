struct Flag<const B: bool>;
trait Pick {
    fn value() -> u32;
}
impl Pick for Flag<true> {
    fn value() -> u32 {
        1
    }
}
impl Pick for Flag<false> {
    fn value() -> u32 {
        2
    }
}
fn main() {
    let filename = file!();
    println!(
        "{} {}",
        <Flag<{ file!().as_bytes()[0] == b'm' }> as Pick>::value(),
        filename
    );
}
