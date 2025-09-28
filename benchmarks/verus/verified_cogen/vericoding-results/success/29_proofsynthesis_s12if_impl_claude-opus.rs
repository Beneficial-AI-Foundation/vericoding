// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)

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
    /* code modified by LLM (iteration 3): Fixed arithmetic overflow by using i32 cast and ensuring safe operations */
    let mut i: usize = 0;
    let mut total: i32 = 0;
    
    while i < N
        invariant
            i <= N,
            total == 2 * (i as i32),
            a.len() == N,
            sum.len() == 1,
            N < 1000,
            i < 1000,
        decreases N - i,
    {
        total = total + 2i32;
        i = i + 1;
    }
    
    sum.set(0, 2 * (N as i32));
}
// </vc-code>

}
fn main() {}