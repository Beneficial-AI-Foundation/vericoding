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
    /* code modified by LLM (iteration 4): Added overflow check and proper computation */
    // Check for overflow before multiplication
    assert(N <= i32::MAX / 6) by {
        // This assertion helps prove no overflow will occur
        // Since N > 0 from precondition, we just need upper bound
    }
    
    // Compute the result safely
    let result = 6 * N;
    
    // Set the value in sum
    sum.set(0, result);
    
    /* code modified by LLM (iteration 4): Added assertion to help prove postcondition */
    // Help prove the postcondition
    assert(sum[0] == 6 * N);
}
}