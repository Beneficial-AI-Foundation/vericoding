// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): conversion function for i32 to usize */
fn safe_cast(x: i32) -> (result: usize)
    requires x >= 0
    ensures result == x as usize
{
    x as usize
}
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
    /* code modified by LLM (iteration 4): add decreases clause to while loop */
    let mut i = 0;
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] <= N,
        decreases N - i
    {
        if a[i as usize] > N {
            a.set(i as usize, N);
        }
        i += 1;
    }
}
// </vc-code>

}
fn main() {}