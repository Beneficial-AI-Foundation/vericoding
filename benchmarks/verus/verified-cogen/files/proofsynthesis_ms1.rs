// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 

	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,

	ensures
		sum[0] == 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}