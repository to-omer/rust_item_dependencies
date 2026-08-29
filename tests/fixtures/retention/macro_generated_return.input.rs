macro_rules! inner{()=>{return;};}macro_rules! outer{()=>{inner!();};}fn run(){outer!();panic!("unreachable");}fn main(){run();println!("ok");}
