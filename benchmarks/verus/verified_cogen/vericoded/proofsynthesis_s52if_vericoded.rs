// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fix return type to nat to match 6*n result and avoid type mismatch */
spec fn six(n: nat) -> nat { 6 * n }
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] == 6 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute 6*N and store into sum[0] safely */
    sum[0] = 6 * (N as i32);
}
// </vc-code>

}
fn main() {}