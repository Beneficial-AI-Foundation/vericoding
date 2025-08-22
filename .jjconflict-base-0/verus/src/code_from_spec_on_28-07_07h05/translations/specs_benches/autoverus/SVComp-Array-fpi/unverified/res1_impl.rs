use vstd::prelude::*;
fn main() {}
verus!{
//IMPL myfun
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
	ensures
		sum[0] <= 2 * N,
{
    /* code modified by LLM (iteration 1): Use i64 arithmetic to avoid overflow, then cast to i32 */
    let result = (2i64 * N as i64) as i32;
    sum.set(0, result);
}
}