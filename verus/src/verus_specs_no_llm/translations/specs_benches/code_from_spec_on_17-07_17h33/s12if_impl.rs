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
		sum[0] == 2 * N,
{
    /* code modified by LLM (iteration 4): Added overflow check and proper arithmetic handling */
    assert(N > 0);
    assert(N <= i32::MAX / 2); // Ensure no overflow when multiplying by 2
    let result = 2 * N;
    sum.set(0, result);
    /* code modified by LLM (iteration 4): Added assertion to help prove postcondition */
    assert(sum[0] == result);
    assert(result == 2 * N);
}
}