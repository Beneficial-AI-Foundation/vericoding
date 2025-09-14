// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): trivial lemma that 0 <= 4*n when n >= 0 */
proof fn four_times_nonneg(n: i32)
    requires
        n >= 0,
    ensures
        0 <= 4 * n,
{
}

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 

	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,

	ensures
		sum[0] <= 4 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): set sum[0] to 0 and prove 0 <= 4*N using lemma */
    proof {
        assert(sum.len() == 1);
        four_times_nonneg(N);
    }
    sum[0] = 0;
}

// </vc-code>

}
fn main() {}