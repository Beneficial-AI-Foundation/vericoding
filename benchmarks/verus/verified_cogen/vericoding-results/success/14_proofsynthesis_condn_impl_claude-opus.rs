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
{
    /* code modified by LLM (iteration 4): Fixed type error by using usize for indexing */
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            a.len() == N,
            i <= n,
            forall |k: int| 0 <= k < i ==> a@[k as int] <= N,
        decreases n - i,
    {
        if a[i] > N {
            a.set(i, N);
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}