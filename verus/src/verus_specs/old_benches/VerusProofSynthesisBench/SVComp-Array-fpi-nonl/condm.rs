use vstd::prelude::*;

verus!{
	fn myfun(a: &mut Vec<i32>, N: u32)
		// pre-conditions-start
		requires
			N > 0,
			old(a).len() == N,
		// pre-conditions-end
		// post-conditions-start
		ensures
			forall |k:int| 0 <= k < N ==> a[k] % 2 == N % 2,
		// post-conditions-end
	{
    // TODO: Remove this comment and implement the function body
	}
}

fn main() {}