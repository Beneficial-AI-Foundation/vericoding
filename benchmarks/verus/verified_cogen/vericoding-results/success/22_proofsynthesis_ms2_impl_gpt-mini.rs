// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
fn min_usize(a: usize, b: usize) -> usize { if a < b { a } else { b } }
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
    sum.push(0);
}
// </vc-code>

}
fn main() {}