macro_rules! effect{()=>{side_effect();};}fn side_effect(){println!("effect");}fn main(){effect!();}
