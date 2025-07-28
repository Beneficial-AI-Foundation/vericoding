use vstd::prelude::*;

verus!{
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	// pre-conditions-start
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
	// pre-conditions-end
	// post-conditions-start
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == 0,
	// post-conditions-end
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

fn main() {}