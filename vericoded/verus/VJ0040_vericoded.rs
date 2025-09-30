// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define function computing 4*n with named return for postcondition */
fn four_times(n: i32) -> (res: i32)
    requires
        n > 0,
        n < 1000,
    ensures
        res == 4 * n,
{
    let two = n + n;
    let four = two + two;
    four
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
        sum[0] == 4 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): set sum[0] to four_times(N) after checking bounds */
    assert(sum.len() == 1usize);
    let val = four_times(N);
    sum.set(0usize, val);
}
// </vc-code>

}
fn main() {}