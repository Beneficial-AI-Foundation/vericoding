// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		forall |k:int| 0 <= k < N ==> a[k] == 2 * N + 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed type consistency and loop invariants */
    let mut i: usize = 0;
    let n_usize = N as usize;
    let value = 2 * N + 1;
    
    while i < n_usize
        invariant
            0 <= i <= n_usize,
            a.len() == n_usize,
            forall |k: int| 0 <= k < i ==> a@[k] == value,
        decreases n_usize - i
    {
        a.set(i, value);
        i += 1;
    }
}
// </vc-code>

}
fn main() {}