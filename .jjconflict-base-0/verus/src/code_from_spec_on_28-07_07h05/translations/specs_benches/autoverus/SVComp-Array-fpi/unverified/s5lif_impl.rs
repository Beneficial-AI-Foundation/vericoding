use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
	ensures
		sum[0] == 6 * N,
{
    /* code modified by LLM (iteration 4): Added overflow check and used spec multiplication to handle arithmetic safely */
    // First, we need to ensure that 6 * N doesn't overflow
    // Since N > 0 and we need 6 * N to fit in i32, we need N <= i32::MAX / 6
    assert(N <= i32::MAX / 6);
    
    // Now we can safely perform the multiplication
    sum[0] = (6 * N) as i32;
}
}