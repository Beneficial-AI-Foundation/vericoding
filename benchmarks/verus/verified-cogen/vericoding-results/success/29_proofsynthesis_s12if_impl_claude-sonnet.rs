// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed for this implementation */
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] == 2 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed ghost variables and proof blocks, use simple loop */
    let mut i: usize = 0;
    while i < N
        invariant
            i <= N,
            a.len() == N,
            sum.len() == 1,
        decreases N - i
    {
        i = i + 1;
    }
    sum.set(0, (2 * N) as i32);
}
// </vc-code>

}
fn main() {}