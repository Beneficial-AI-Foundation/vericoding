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
		forall |k:int| 0 <= k < N ==> a[k] == N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let n = N as usize;
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == N,
            sum.len() == 1,
            0 <= i <= n,
            n == N as usize,
            forall |k: int| 0 <= k < i ==> a[k as int] == N,
        decreases n - i
    {
        a.set(i, N);
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}