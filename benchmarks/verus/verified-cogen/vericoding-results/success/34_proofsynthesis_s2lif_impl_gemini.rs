// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] == 3 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used `int` cast in invariant to aid arithmetic reasoning and prevent overflow errors */
    let mut i: i32 = 0;
    sum.set(0, 0);
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            (N as int) < 1000,
            sum[0] as int == 3 * (i as int),
        decreases N - i,
    {
        let current_sum = sum[0];
        sum.set(0, current_sum + 3);

        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}