// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fix pre-state reference for &mut param and set first element */
fn set_first(sum: &mut Vec<i32>, val: i32)
    requires
        old(sum).len() >= 1,
    ensures
        sum[0] == val,
{
    sum[0] = val;
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

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
    /* code modified by LLM (iteration 2): set first element to 2*N using helper, relying on precondition old(sum).len() == 1 */
    let two_n: i32 = 2 * N;
    set_first(sum, two_n);
}
// </vc-code>

}
fn main() {}