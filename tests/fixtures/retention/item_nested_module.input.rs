fn dead_first(){}mod kept{fn dead_module_first(){}pub fn entry(){fn dead_nested(){}helper()}fn helper(){}fn dead_module_last(){}}fn main(){kept::entry()}fn dead_last(){}
