use vstd::prelude::*;
fn main() {}
verus!{
//IMPL myfun
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		/* code modified by LLM (iteration 1): added overflow prevention constraint */
		N <= i32::MAX / 6,
	ensures
		sum[0] == 6 * N,
{
    /* code modified by LLM (iteration 1): computation with overflow check */
    let result = 6 * N;
    sum.set(0, result);
}
}