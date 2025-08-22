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
    let mut i: usize = 0;
    /* code modified by LLM (iteration 1): Added decreases clause to prove loop termination */
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == N,
        decreases a.len() - i,
    {
        a.set(i, N);
        i = i + 1;
    }
}
}