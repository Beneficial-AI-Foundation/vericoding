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
    /* code modified by LLM (iteration 3): fixed arithmetic overflow by adding bounds check */
    let mut i: usize = 0;
    let n_usize = N as usize;
    let mut total: i32 = 0;
    
    while i < n_usize
        invariant
            i <= n_usize,
            n_usize == N as usize,
            a.len() == N,
            sum.len() == 1,
            total == 4 * (i as i32),
            i <= 1000,
            N < 1000,
        decreases n_usize - i,
    {
        a.set(i, 4);
        assert(i < 1000);
        assert(4 * i < 4000);
        total = total + 4;
        i = i + 1;
    }
    
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}