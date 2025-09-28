// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] == 4 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed arithmetic overflow and loop invariant by using proper Vec indexing and ensuring no overflow */
    *sum = vec![0];
    for i in 0..N
        invariant
            sum.len() == 1,
            sum[0] == 4 * (i as i32),
            i <= N,
            N < 1000,
    {
        sum[0] = sum[0] + 4;
    }
}
// </vc-code>

}
fn main() {}