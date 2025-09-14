// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed unused vector parameter to fix precondition in recursive call */
fn accumulate_sum(n: i32) -> (result: i32)
    requires
        n > 0,
        n < 1000,
    ensures
        result == 3 * n,
    decreases n,
{
    if n == 1 {
        3
    } else {
        accumulate_sum(n - 1) + 3
    }
}
// </vc-helpers>

// <vc-spec>
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] == 3 * N,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): updated to use helper without vector parameter */
{
    *sum = vec![accumulate_sum(N)];
}
// </vc-code>

}
fn main() {}