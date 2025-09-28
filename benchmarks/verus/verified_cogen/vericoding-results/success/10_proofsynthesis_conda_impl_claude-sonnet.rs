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
    /* code modified by LLM (iteration 5): fix invariant and overflow by using proper bounds */
    let mut i: i32 = 0;
    let mut total: i32 = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            total == 2 * i,
            a.len() == N,
            sum.len() == 1,
            N < 1000,
            i < 1000,
            total < 2000,
        decreases N - i
    {
        total = total + 2;
        i = i + 1;
    }
    
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}