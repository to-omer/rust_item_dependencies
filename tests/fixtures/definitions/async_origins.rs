async fn direct() {}

macro_rules! make_async {
    () => {
        async fn generated() {}
    };
}

make_async!();

fn main() {
    let _ = direct();
    let _ = generated();
    let _ = async {};
}
