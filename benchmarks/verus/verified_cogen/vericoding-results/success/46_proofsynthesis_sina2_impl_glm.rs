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
    /* code modified by LLM (iteration 3): removed assertion that was failing and simplified loop */
    let value = N + 1;
    for i in 0..(N as usize)
        invariant
            a.len() == N,
            forall |k: int| 0 <= k < i ==> a@[k] == value,
    {
        a.set(i, value);
    }
}
// </vc-code>

}
fn main() {}