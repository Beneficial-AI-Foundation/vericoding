// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): use mathematical int for doubling and provide lemma to ensure no overflow */
spec fn times_two(n: int) -> int { 2 * n }
proof fn times_two_fits(n: i32)
    requires
        n > 0,
        n < 1000,
    ensures
        2 * n <= 1998,
        2 * n >= -1998,
{
}

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		sum[0] == 2 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): call proof lemma to ensure doubling won't overflow, then assign */
    proof {
        times_two_fits(N);
    }
    sum[0] = 2 * N;
}

// </vc-code>

}
fn main() {}