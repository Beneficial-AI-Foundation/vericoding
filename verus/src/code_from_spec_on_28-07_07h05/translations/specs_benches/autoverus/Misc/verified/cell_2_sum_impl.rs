use vstd::prelude::*;
fn main() {}
verus!{

//IMPL myfun
pub fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
	requires 
		old(a).len() == N,
		N <= 0x7FFF_FFFF,
	ensures
	    sum <= 2*N,
{
    0
}
}