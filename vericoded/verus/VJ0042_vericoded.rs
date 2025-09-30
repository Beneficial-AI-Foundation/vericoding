// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): use named return variable to avoid 'result' binding issue and preconditions to prevent i32 overflow */
fn times_five(x: i32) -> (r: i32)
    requires
        0 <= x,
        x < 1000,
    ensures
        r == 5 * x
{
    5 * x
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
		sum[0] == 5 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute 5*N using helper and write to sum[0] */
    assert(N > 0);
    assert(0 <= N);
    assert(N < 1000);
    let val = times_five(N);
    assert(sum.len() == 1);
    let idx: usize = 0;
    sum.set(idx, val);
}
// </vc-code>

}
fn main() {}