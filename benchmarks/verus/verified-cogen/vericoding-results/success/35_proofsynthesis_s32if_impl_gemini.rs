// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added invariant y < 1000 to prove absence of overflow. */
fn mul_by_add(y: usize) -> (res: i32)
    requires y < 1000,
    ensures res == 4 * (y as i32),
{
    let mut i: usize = 0;
    let mut res: i32 = 0;
    while i < y
        invariant
            i <= y,
            y < 1000, 
            res == 4 * (i as i32),
        decreases y - i
    {
        res = res + 4;
        i = i + 1;
    }
    res
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
		sum[0] == 4 * N,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Implementation is correct, no changes needed. */
{
    let total = mul_by_add(N);
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}