use vstd::prelude::*;

verus!{
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
		forall |k:int| 0 <= k < N ==> a[k] == 2 * N + 1,
	// post-conditions-end
{
    let target_value = 2 * N + 1;
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): simplified loop with cleaner proof structure */
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == 2 * N + 1,
        decreases N - i,
    {
        /* code modified by LLM (iteration 4): set value and increment without problematic assertions */
        let idx = i as usize;
        a.set(idx, target_value);
        i += 1;
    }
}
}

fn main() {}