// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
spec fn zero_le_4n(N: int) -> bool { 0 <= 4 * N }
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 

	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,

	ensures
		sum[0] <= 4 * N,
// </vc-spec>
// <vc-code>
{
    sum.clear();
    sum.push(0);
}
// </vc-code>

}
fn main() {}