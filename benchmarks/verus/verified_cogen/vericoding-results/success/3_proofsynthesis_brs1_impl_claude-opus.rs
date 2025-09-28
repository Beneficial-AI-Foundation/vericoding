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

    ensures
        sum[0] <= N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed invariant and cast issues */
    let mut i: usize = 0;
    let mut count: i32 = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N as usize,
            sum.len() == 1,
            count >= 0,
            count <= N,
            i <= N as usize,
            count <= i as i32,
        decreases a.len() - i,
    {
        if i < a.len() && a[i] == 1 {
            count = count + 1;
        }
        i = i + 1;
    }
    
    sum.set(0, count);
}
// </vc-code>

}
fn main() {}