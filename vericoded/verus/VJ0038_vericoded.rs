// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): use mathematical int to avoid overflow in triple */
spec fn triple(x: int) -> int { 3 * x }
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,

    ensures
        sum[0] == 3 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute sum directly as 3*N to avoid loop arithmetic overflow */
    sum.clear();
    sum.push(3 * N);
}
// </vc-code>

}
fn main() {}