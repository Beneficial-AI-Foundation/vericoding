use vstd::prelude::*;

verus!{

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut i = 0;
    /* code modified by LLM (iteration 2): added decreases clause for loop termination */
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k as int] % 2 == N % 2,
        decreases N - i,
    {
        if N % 2 == 0 {
            a.set(i as usize, 2);
        } else {
            a.set(i as usize, 1);
        }
        i = i + 1;
    }
    // impl-end
}
// </vc-code>

}

fn main() {}