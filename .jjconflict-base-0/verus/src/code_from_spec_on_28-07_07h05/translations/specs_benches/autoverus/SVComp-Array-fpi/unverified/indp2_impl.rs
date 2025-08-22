use vstd::prelude::*;
fn main() {}
verus!{
//IMPL myfun
pub fn myfun(a: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == 0,
{
    let mut i = 0;
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == 0,
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases N - i,
    {
        a.set(i as usize, 0);
        i = i + 1;
    }
}
}