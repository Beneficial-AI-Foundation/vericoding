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
		forall |k:int| 0 <= k < N ==> a[k] == N + 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed type casting and overflow issues */
    let mut i: usize = 0;
    let n_val = (N + 1) as i32;
    while i < N as usize
        invariant
            0 <= i <= N,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < i ==> a@[k] == n_val,
        decreases N as usize - i
    {
        a[i] = n_val;
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}