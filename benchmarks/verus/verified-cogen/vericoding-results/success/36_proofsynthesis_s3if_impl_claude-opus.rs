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
        sum[0] == 3 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed arithmetic overflow and invariant */
    let mut i: usize = 0;
    let mut total: i32 = 0;
    
    while i < N as usize
        invariant
            i <= N as usize,
            a.len() == N,
            sum.len() == 1,
            total == 3 * (i as i32),
            N < 1000,
            i <= 1000,
        decreases N as usize - i,
    {
        proof {
            assert(i < N as usize);
            assert(N < 1000);
            assert(i < 1000);
            assert(3 * i < 3000);
            assert(total == 3 * (i as i32));
            assert(total < 3000);
            assert(total + 3 < i32::MAX);
        }
        total = total + 3;
        i = i + 1;
    }
    
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}