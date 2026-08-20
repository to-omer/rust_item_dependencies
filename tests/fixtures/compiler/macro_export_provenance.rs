#[macro_export]
macro_rules! exported {
    () => {
        1_u8
    };
}

mod caller {
    use crate::exported as alias;

    pub fn run() {
        let _ = alias!();
    }
}

fn main() {
    caller::run();
}
