macro_rules! consume{(x $($rest:tt)*)=>{{;}};}fn main(){consume!(x );println!("ok");}
