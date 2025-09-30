// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
proof fn lemma_nonneg_times4(n: i32)
    requires
        n > 0
    ensures
        0 <= 4 * n
{ }
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
    proof {
        assert(sum.len() == 1);
    }
    sum[0] = 0;
    proof {
        lemma_nonneg_times4(N);
    }
}
// </vc-code>

}
fn main() {}