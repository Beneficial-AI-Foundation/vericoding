// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

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
    /* code modified by LLM (iteration 2): Remove mutable reference handling that Verus doesn't support */
    sum[0] = 4 * N;
}
// </vc-code>

}
fn main() {}