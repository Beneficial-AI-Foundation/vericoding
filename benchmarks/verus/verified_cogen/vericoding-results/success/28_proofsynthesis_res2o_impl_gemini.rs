// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 3): changed invariant to use `int` casts and added invariant on N to prove absence of overflow */
{
    let mut s: i32 = 0;
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            s as int == 3 * (i as int),
            N < 1000, // bring precondition into loop to prove bounds
        decreases N - i
    {
        s = s + 3;
        i = i + 1;
    }
    sum.set(0, s);
}
// </vc-code>

}
fn main() {}