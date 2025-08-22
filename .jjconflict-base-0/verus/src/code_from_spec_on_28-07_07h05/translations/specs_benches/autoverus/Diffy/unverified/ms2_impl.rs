use vstd::prelude::*;
fn main() {}
verus!{

//IMPL myfun
pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
	ensures
		sum[0] <= N,
{
    sum.set(0, 0);
}
}