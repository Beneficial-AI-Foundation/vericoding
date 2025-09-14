// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): use old(sum) in requires to refer to pre-state length and safely set sum[0] = 2*N */
fn set_sum_with_two_n(sum: &mut Vec<i32>, N: i32)
    requires
        old(sum).len() == 1,
        N > 0,
        N < 1000,
    ensures
        sum.len() == 1,
        sum[0] == 2 * N
{
    sum[0] = 2 * N;
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 

	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,

	ensures
		sum[0] <= 2 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): set sum[0] to 2*N via helper; ensures condition holds */
    set_sum_with_two_n(sum, N);
}
// </vc-code>

}
fn main() {}