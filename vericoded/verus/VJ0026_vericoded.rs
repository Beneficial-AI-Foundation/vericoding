// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
proof fn lemma_zero_le_two_n(n: i32)
    requires
        n > 0,
        n < 1000,
    ensures
        0 <= 2 * n
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
		sum[0] <= 2 * N,
// </vc-spec>
// <vc-code>
{
    sum.clear();
    sum.push(0i32);
    assert(sum.len() == 1);
    sum[0] = 0i32;
    proof { lemma_zero_le_two_n(N); }
}
// </vc-code>

}
fn main() {}