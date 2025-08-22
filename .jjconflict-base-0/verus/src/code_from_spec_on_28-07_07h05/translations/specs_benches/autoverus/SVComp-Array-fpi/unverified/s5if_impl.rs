use vstd::prelude::*;
fn main() {}
verus!{
//IMPL myfun
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
	ensures
		sum[0] == 5 * N,
{
    /* code modified by LLM (iteration 4): Direct assignment using i32 arithmetic to match postcondition */
    sum.set(0, 5 * N);
}
}