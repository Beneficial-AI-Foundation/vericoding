// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 

	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,

	ensures
		sum[0] <= 4 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added N < 1000 to the loop invariant to prevent a potential arithmetic overflow error. */
    sum.set(0, 0);
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            sum.len() == 1,
            a.len() == N,
            N < 1000,
            sum[0] == 4 * i,
        decreases N - i,
    {
        a.set(i as usize, 4);
        let temp_sum = sum[0];
        sum.set(0, temp_sum + 4);
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}