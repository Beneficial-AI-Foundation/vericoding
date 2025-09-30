// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
spec fn triple(a: int) -> int { 3 * a }

proof fn triple_additive(a: int, b: int)
    ensures
        triple(a + b) == triple(a) + triple(b)
{
}
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
    let val: i32 = N * 3;
    sum[0usize] = val;
}
// </vc-code>

}
fn main() {}