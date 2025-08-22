use vstd::prelude::*;

verus!{
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	// pre-conditions-start
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	// pre-conditions-end
	// post-conditions-start
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == N + 1,
	// post-conditions-end
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == N + 1,
            /* code modified by LLM (iteration 1): added bounds check to prevent overflow */
            N + 1 <= i32::MAX,
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases a.len() - i
    {
        /* code modified by LLM (iteration 1): cast N to i32 and add assertion to help verification */
        assert(i < a.len());
        assert(N + 1 <= i32::MAX);
        a.set(i, N + 1);
        /* code modified by LLM (iteration 1): add assertion to help prove invariant maintenance */
        assert(forall |k:int| 0 <= k < i ==> a[k] == N + 1);
        assert(a[i as int] == N + 1);
        i += 1;
        /* code modified by LLM (iteration 1): assertion to maintain invariant after increment */
        assert(forall |k:int| 0 <= k < i ==> a[k] == N + 1);
    }
}
}

fn main() {}