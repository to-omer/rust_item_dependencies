macro_rules! define_late_alias {
    () => {
        use std::eprintln as late_alias;
    };
}

fn call_before_definition() {
    late_alias!("retry");
}

define_late_alias!();

fn main() {
    call_before_definition();
}
