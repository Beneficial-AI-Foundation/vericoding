// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
proof fn lemma_pos_implies_le_double(n: i32)
    requires n > 0
    ensures n <= 2 * n
{ }
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
		sum[0] <= 2 * N,
// </vc-spec>
// <vc-code>
{
    sum[0] = N;
    proof { lemma_pos_implies_le_double(N); }
}
// </vc-code>

}
fn main() {}