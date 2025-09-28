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
		forall |k:int| 0 <= k < N ==> a[k] == N + 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed arithmetic overflow and loop invariant maintenance */
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            N < 1000,
            forall |k:int| 0 <= k < i ==> a@[k as int] == (N + 1) as i32,
        decreases N - i
    {
        a.set(i as usize, (N + 1) as i32);
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}