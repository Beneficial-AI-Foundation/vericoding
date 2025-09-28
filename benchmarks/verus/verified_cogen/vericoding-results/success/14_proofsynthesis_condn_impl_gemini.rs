// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, N: i32, m: i32)

	requires
		N > 0,
		old(a).len() == N,

	ensures
		forall |k:int| 0 <= k < N ==> a[k] <= N,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed while loop syntax by reordering invariant and decreases clauses */
{
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            a.len() as i32 == N,
            forall|k: int| 0 <= k < i ==> a[k] <= N,
        decreases N - i
    {
        if a[i as usize] > N {
            a.set(i as usize, N);
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}