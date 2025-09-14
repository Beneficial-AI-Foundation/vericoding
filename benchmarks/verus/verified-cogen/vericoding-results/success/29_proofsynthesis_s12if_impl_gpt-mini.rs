// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): returns 2*n as int */ spec fn times_two(n: nat) -> int { 2 * (n as int) }
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)

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
    /* code modified by LLM (iteration 4): compute and set sum[0] to 2*N */
    let v: i32 = 2 * (N as i32);
    sum[0] = v;
}
// </vc-code>

}
fn main() {}