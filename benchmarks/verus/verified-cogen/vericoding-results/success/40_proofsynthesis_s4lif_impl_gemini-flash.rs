// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,

    ensures
        sum[0] == 5 * N,
// </vc-spec>
// <vc-code>
{
    let mut i: i32 = 0;
    sum.set(0, 0);

    while i < N
         invariant
             0 <= i <= N,
             a.len() == N as nat,
             sum.len() == 1,
             sum[0] == 5 * i,
             N < 1000,
         decreases N - i
    {
        a.set(i as usize, 5);
        let temp_sum_val: i32 = sum[0];
        sum.set(0, temp_sum_val + a[i as usize]);
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}