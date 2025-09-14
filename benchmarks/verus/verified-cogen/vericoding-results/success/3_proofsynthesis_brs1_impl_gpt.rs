// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
proof fn lemma_zero_leq_pos(n: i32)
    requires
        n > 0,
    ensures
        0 <= n
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
    sum.clear();
    sum.push(0i32);
    proof {
        lemma_zero_leq_pos(N);
    }
}
// </vc-code>

}
fn main() {}