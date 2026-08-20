const fn sibling_dependency()->u32{7}std::thread_local!{static KEPT:u32=1;static SIBLING:u32=sibling_dependency();}fn dead(){}fn main(){KEPT.with(|value|{let _=*value;});}
