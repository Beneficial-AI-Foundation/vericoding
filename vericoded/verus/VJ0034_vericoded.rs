// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,

	ensures
		sum[0] == N,
// </vc-spec>
// <vc-code>
{
    sum.clear();
    sum.push(N);
}
// </vc-code>

}
fn main() {}