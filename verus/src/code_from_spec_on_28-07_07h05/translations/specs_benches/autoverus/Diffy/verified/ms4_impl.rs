use vstd::prelude::*;
fn main() {}
verus!{

//IMPL myfun
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	ensures
		sum[0] <= 3 * N,
{
    sum.set(0, 0);
}
}