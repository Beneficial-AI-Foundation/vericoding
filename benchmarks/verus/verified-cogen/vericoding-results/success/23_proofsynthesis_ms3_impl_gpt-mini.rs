// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): prove nonnegativity of 2*N for N>0 */
proof fn zero_le_two_times_n(N: i32)
    requires
        N > 0,
    ensures
        0 <= 2 * N,
    decreases
        N
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
		sum[0] <= 2 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): set sum[0] to 0 and prove it's <= 2*N using helper */
    sum.clear();
    sum.push(0);
    proof {
        zero_le_two_times_n(N);
        assert(sum.len() == 1);
        assert(sum[0] == 0);
        assert(sum[0] <= 2 * N);
    }
}

// </vc-code>

}
fn main() {}