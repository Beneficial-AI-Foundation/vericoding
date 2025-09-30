// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
proof fn lemma_zero_leq_usize(n: usize) ensures 0 <= n { }
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 

	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,

	ensures
		sum[0] <= N,
// </vc-spec>
// <vc-code>
{
    sum.clear();
    sum.push(0usize);
}
// </vc-code>

}
fn main() {}