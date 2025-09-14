// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)

    requires 
        old(a).len() == N,
        N <= 0x7FFF_FFFF,

    ensures
        sum <= 2*N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): strengthened invariants with nat to prove non-overflow */
    let mut i: u32 = 0;
    let mut sum: u32 = 0;
    while i < N
        invariant
            i <= N,
            a.len() == N as usize,
            (sum as nat) <= 2 * (i as nat),
            (N as nat) <= 0x7FFF_FFFF,
        decreases N - i,
    {
        let val = a[i as usize];
        let to_add = if val > 2 { 2 } else { val };
        sum = sum + to_add;
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}