use vstd::prelude::*;
fn main() {}
verus!{
//IMPL myfun
pub fn myfun(a: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] <= N,
{
    /* code modified by LLM (iteration 2): Added decreases clause to prove loop termination */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] <= N,
        decreases a.len() - i
    {
        if a[i] > N {
            a.set(i, N);
        }
        i = i + 1;
    }
}
}