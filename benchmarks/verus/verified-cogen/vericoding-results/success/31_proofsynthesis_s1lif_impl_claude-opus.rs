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
		sum[0] == 2 * N,
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut total: i32 = 0;
    
    /* code modified by LLM (iteration 3): Fixed arithmetic overflow and invariant maintenance */
    while i < N as usize
        invariant
            i <= N as usize,
            a.len() == N,
            sum.len() == 1,
            total == 2 * (i as i32),
            N < 1000,
            i <= 1000,
        decreases N as usize - i,
    {
        total = total + 2;
        i = i + 1;
    }
    
    sum[0] = total;
}
// </vc-code>

}
fn main() {}