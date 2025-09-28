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
		sum[0] <= 3 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added precondition to loop invariant to resolve overflow error */
    let mut i: i32 = 0;
    let mut temp_sum: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            N < 1000,
            temp_sum == 3 * i,
        decreases N - i
    {
        temp_sum = temp_sum + 3;
        i = i + 1;
    }
    assert(temp_sum == 3 * N);
    sum.set(0, temp_sum);
}
// </vc-code>

}
fn main() {}