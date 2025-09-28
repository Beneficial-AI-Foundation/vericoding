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
    /* code modified by LLM (iteration 5): added an explicit bound on sum[0] to the loop invariant to prove absence of overflow */
    let mut i: i32 = 0;
    sum.set(0, 0);
    while i < N
        invariant
            0 <= i <= N,
            N < 1000,
            sum.len() == 1,
            a.len() == N,
            sum[0] as int == 4 * (i as int),
            sum[0] < 4000, 
        decreases N - i,
    {
        let s = sum[0];
        sum.set(0, s + 4);
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}