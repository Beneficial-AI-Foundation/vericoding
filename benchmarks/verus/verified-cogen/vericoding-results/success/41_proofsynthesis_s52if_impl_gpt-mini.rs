// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): commutativity of multiplication with casted usize */
proof fn mul_cast_comm(n: usize)
    ensures
        (n as i32) * 6 == 6 * (n as i32),
{
    assert((n as i32) * 6 == 6 * (n as i32));
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
		sum[0] == 6 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): set sum to single element equal to 6 * N */
    sum.clear();
    sum.push(6 * (N as i32));
}
// </vc-code>

}
fn main() {}