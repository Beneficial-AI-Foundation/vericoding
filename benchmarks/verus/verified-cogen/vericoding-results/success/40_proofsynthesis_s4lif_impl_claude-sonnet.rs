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
        sum[0] == 5 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed overflow by ensuring addition stays within bounds and fixed invariant to properly track progress */
    let mut i: usize = 0;
    sum.set(0, 0);
    
    while i < N as usize
        invariant
            0 <= i <= N,
            sum[0] == 5 * (i as i32),
            a.len() == N,
            sum.len() == 1,
            N < 1000,
            i < 1000,
        decreases N as usize - i
    {
        a.set(i, 5);
        let current_sum = sum[0];
        proof {
            assert(current_sum == 5 * (i as i32));
            assert(i < N);
            assert(N < 1000);
            assert(current_sum + 5 == 5 * ((i + 1) as i32));
        }
        sum.set(0, current_sum + 5);
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}