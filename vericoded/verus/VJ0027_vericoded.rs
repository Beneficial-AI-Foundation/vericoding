// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): pure spec helper asserting positivity */
spec fn is_pos(n: int) -> bool { n > 0 }
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
    /* code modified by LLM (iteration 4): set sum[0] to N which is <= 3*N for N>0 */
    sum.clear();
    sum.push(N);
}
// </vc-code>

}
fn main() {}