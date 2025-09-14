// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no changes needed */
proof fn safe_cast(n: usize)
    requires n < 1000,
    ensures 3 * (n as int) <= 2997,
{
    assert(n <= 999);
    assert(3 * (n as int) <= 3 * 999);
    assert(3 * 999 == 2997);
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)

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
    /* code modified by LLM (iteration 3): removed unsupported &mut usage */
    proof {
        safe_cast(N);
    }
    sum[0] = (3 * N) as i32;
}
// </vc-code>

}
fn main() {}