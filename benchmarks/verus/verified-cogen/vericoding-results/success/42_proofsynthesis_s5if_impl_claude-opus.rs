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
		sum[0] == 5 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed type error by using i32 for loop counter instead of nat */
    let mut i: i32 = 0;
    sum[0] = 0;
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            sum[0] == 5 * i,
            N < 1000,
        decreases N - i,
    {
        sum[0] = sum[0] + 5;
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}