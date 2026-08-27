#[derive(Default)]
enum ConfiguredDefault {
    #[cfg_attr(all(), default)]
    Active,
    Other,
}

#[cfg_attr(all(), derive(Clone, Hash))]
struct ConfiguredDerives;

#[derive(Clone)]
#[cfg_attr(all(), derive(Hash))]
struct DirectThenConfigured;

#[cfg_attr(all(), derive(Hash))]
#[derive(Clone)]
struct ConfiguredThenDirect;

macro_rules! make_generated {
    () => {
        #[derive(Clone, Default)]
        struct Generated;
    };
}

make_generated!();

fn unused() {}

fn main() {
    let configured = ConfiguredDefault::Active;
    assert!(matches!(configured, ConfiguredDefault::Active));
    let _ = ConfiguredDerives.clone();
    let _ = DirectThenConfigured.clone();
    let _ = ConfiguredThenDirect.clone();
    let _ = Generated;
    println!("ok");
}
