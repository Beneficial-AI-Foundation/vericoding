// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
proof fn zero_le_five_mul(N: int)
    requires
        N > 0,
    ensures
        0 <= 5 * N,
{
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
		sum[0] <= 5 * N,
// </vc-spec>
// <vc-code>
{
    sum[0] = 0;
}

// </vc-code>

}
fn main() {}