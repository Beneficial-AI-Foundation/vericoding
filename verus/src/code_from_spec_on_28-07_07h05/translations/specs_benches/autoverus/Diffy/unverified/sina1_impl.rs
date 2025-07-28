use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == N,
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == N,
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases a.len() - i
    {
        a.set(i, N);
        i += 1;
    }
}
}