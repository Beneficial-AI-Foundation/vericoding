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
    /* code modified by LLM (iteration 3): added invariant and assert for arithmetic */
    let mut i: i32 = 0;
    sum.set(0, 0);
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            N < 1000,
            sum[0] == 4 * i
        decreases N - i
    {
        let temp = sum[0];
        sum.set(0, temp + 4);
        i = i + 1;
        assert(4 * i == 4 * (i - 1) + 4);
    }
}
// </vc-code>

}
fn main() {}