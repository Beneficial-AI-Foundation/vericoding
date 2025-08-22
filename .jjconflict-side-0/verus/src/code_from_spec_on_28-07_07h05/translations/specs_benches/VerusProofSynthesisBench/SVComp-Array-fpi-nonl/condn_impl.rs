use vstd::prelude::*;

verus!{
fn myfun(a: &mut Vec<i32>, N: i32, m: i32)
	// pre-conditions-start
	requires
		N > 0,
		old(a).len() == N,
	// pre-conditions-end
	// post-conditions-start
	ensures
		forall |k:int| 0 <= k < N ==> a[k] <= N,
	// post-conditions-end
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] <= N,
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases a.len() - i
    {
        if a[i] > N {
            a.set(i, N);
        }
        i += 1;
    }
}
}

fn main() {}