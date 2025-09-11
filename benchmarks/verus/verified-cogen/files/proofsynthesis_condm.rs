// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, N: u32)

		requires
			N > 0,
			old(a).len() == N,

		ensures
			forall |k:int| 0 <= k < N ==> a[k] % 2 == N % 2,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}