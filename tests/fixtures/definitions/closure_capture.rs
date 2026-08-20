trait Show {}

fn capture(value: &dyn Show) {
    let _ = || value;
}

fn main() {}
