macro_rules! consume{(x $($rest:tt)*)=>{{fn dead(){}consume!($($rest)*);}};()=>{};}fn main(){consume!(x x x);println!("ok");}
