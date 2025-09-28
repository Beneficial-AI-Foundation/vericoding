// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 2): added loop with decreases clause */
{
    let mut i = 0;
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            (forall |k: int| 0 <= k < i ==> a[k] == 2),
        decreases N - i
    {
        a.set(i as usize, 2);
        i = i + 1;
    }
    sum.set(0, 2*N);
}
// </vc-code>

}
fn main() {}