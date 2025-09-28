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

	ensures
		forall |k:int| 0 <= k < N ==> a[k] == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed type mismatch by using @ operator for spec indexing */
    let mut i = 0;
    while i < N
        invariant
            0 <= i <= N,
            forall |k: int| 0 <= k < i ==> a@[k] == 0,
            a.len() == N,
            sum.len() == 1,
        decreases N - i
    {
        a[i as usize] = 0;
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}