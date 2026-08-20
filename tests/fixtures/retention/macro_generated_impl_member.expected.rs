struct Reader;

macro_rules! implement_read {
    () => {
        fn read(&mut self, _: &mut [u8]) -> std::io::Result<usize> {
            Ok(0)
        }
    };
}

impl std::io::Read for Reader {
    implement_read!();
}



fn main() {
    let mut reader = Reader;
    let _: &mut dyn std::io::Read = &mut reader;
}
