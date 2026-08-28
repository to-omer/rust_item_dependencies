macro_rules! stop{()=>{return;};}fn run(){stop!();panic!("unreachable");}fn main(){run();println!("ok");}
