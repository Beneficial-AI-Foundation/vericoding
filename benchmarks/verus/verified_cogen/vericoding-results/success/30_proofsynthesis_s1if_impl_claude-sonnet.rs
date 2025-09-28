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
		sum[0] == N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut i = 0;
    sum[0] = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            sum.len() == 1,
            a.len() == N,
            sum[0] == i,
        decreases N - i
    {
        sum[0] = sum[0] + 1;
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}