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
/* code modified by LLM (iteration 2): added N < 1000 to the loop invariant to help Verus prove that the arithmetic does not overflow */
{
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            N < 1000, // Invariant from requires to prove no overflow
            forall|k: int| 0 <= k < i ==> a[k] == 2 * N + 1
        decreases N - i
    {
        a.set(i as usize, 2 * N + 1);
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}