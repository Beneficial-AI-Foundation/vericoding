// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): provide zero constant helper */
spec fn zero_val() -> i32 { 0 }
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] <= 2 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): set sum[0] to 0 to ensure sum[0] <= 2*N */
    sum.clear();
    sum.push(0);
}

// </vc-code>

}
fn main() {}