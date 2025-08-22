use vstd::prelude::*;
fn main() {}
verus!{
//IMPL myfun
pub fn myfun(a: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == k + 1,
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == k + 1,
        /* code modified by LLM (iteration 1): Added decreases clause to prove loop termination */
        decreases a.len() - i,
    {
        a.set(i, (i + 1) as i32);
        i = i + 1;
    }
}
}