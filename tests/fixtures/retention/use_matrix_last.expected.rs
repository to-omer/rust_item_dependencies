mod 日本{pub mod inner{pub fn alpha(){}pub fn beta(){}pub fn gamma(){}}}
use crate::日本::{self as 名前空間,inner::{alpha as 一, /* 二 */ beta as 二,},*,};
fn main(){}
