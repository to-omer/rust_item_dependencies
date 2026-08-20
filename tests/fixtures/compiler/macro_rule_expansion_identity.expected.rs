macro_rules ! m {  ( ( $ ( $ t : tt ) ,* ) ) => { ( $ ( m ! ( same $ t ) ) ,* ) } ; ( same $ t : tt ) => { m ! ( $ t ) } ; ( wrap ) => { m ! ( base ) } ; ( base ) => { 0usize } ; }
fn main ( ) { let _ = m ! ( ( wrap , base ) ) ; }
