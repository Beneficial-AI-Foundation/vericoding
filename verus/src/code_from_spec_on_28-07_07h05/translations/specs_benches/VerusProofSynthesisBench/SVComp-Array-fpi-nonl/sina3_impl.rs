use vstd::prelude::*;

verus!{
//IMPL myfun
fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	// pre-conditions-start
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,
	// pre-conditions-end
	// post-conditions-start
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == N + 1,
	// post-conditions-end
{
    let mut i = 0;
    /* code modified by LLM (iteration 2): fixed invariant and added overflow bounds */
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            N < 1000,
            /* code modified by LLM (iteration 2): corrected invariant to use a.len() instead of N for bounds */
            forall |k:int| 0 <= k < i ==> a[k as int] == N + 1,
        decreases N - i,
    {
        /* code modified by LLM (iteration 2): added bounds check and overflow safety */
        a.set(i as usize, N + 1);
        i += 1;
    }
}
}

fn main() {}