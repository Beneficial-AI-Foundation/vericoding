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
    /* code modified by LLM (iteration 4): strengthened loop invariant to maintain i < 1000 during loop */
    let mut i: usize = 0;
    sum[0] = 0;
    while i < N
        invariant
            i <= N,
            a.len() == N,
            sum.len() == 1,
            sum[0] == 4i32 * (i as i32),
            i < 1000,
            N < 1000,
        decreases N - i,
    {
        sum[0] = sum[0] + 4i32;
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}