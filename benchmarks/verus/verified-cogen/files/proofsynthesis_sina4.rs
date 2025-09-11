// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		forall |k:int| 0 <= k < N ==> b[k] == N + 2,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}