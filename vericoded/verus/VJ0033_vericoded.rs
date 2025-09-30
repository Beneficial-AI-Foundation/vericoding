// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
proof fn lemma_zero_le_three_n(n: i32)
    requires
        0 < n,
        n < 1000,
    ensures
        0 <= 3 * n
{
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(c).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] <= 3 * N,
// </vc-spec>
// <vc-code>
{
    if sum.len() == 0 {
        sum.push(0);
    } else {
        sum[0] = 0;
    }
    assert(sum.len() >= 1);
    assert(sum[0] == 0);
    proof { lemma_zero_le_three_n(N); }
}
// </vc-code>

}
fn main() {}