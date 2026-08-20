macro_rules! program{()=>{fn main(){needed()}fn needed(){}fn sibling(){sibling_dependency()}}}fn sibling_dependency(){}program!();
