// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): prove non-negativity of N from N > 0 */
proof fn zero_leq(N: i32)
    requires
        N > 0,
    ensures
        0 <= N,
{
}

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,

    ensures
        sum[0] <= N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): set sum[0] to 0 which is <= N */
    sum.clear();
    sum.push(0);
}

// </vc-code>

}
fn main() {}