//IMPL myfun
use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == N + (k + 1) * (k + 1),
{
    let mut i: usize = 0;
    while i < N as usize
        invariant
            i <= N,
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == N + (k + 1) * (k + 1),
        /* code modified by LLM (iteration 3): added decreases clause to prove loop termination */
        decreases N as usize - i
    {
        let k = i as i32;
        /* code modified by LLM (iteration 3): removed int casts and performed calculation directly with i32 */
        let result = N + (k + 1) * (k + 1);
        a.set(i, result);
        i += 1;
    }
}
}