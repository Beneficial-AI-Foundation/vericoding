// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): use named return value for ensures and safe doubling within bounds */
fn double_i32(n: i32) -> (res: i32)
    requires
        0 <= n && n < 1000,
    ensures
        res == n + n,
{
    n + n
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
    /* code modified by LLM (iteration 3): compute 2*N directly and set sum to contain exactly this value */
    let val: i32 = N * 2;
    sum.clear();
    sum.push(val);
}
// </vc-code>

}
fn main() {}