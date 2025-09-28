// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): No changes needed, helper is correct. */
spec fn expected_sum_value(k: i32) -> int { 2 * k }
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
    /* code modified by LLM (iteration 4): Removed modification of 'a' to prevent overflow and added N's bound to the invariant to help prove the sum calculation is safe. */
    sum.set(0, 0);
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            sum[0] == expected_sum_value(i),
            N < 1000,
        decreases N - i
    {
        // The write to a is not required by the ensures clause and causes an overflow error
        // because the initial contents of `a` are not constrained.

        let val_sum = sum[0];
        sum.set(0, val_sum + 2);

        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}