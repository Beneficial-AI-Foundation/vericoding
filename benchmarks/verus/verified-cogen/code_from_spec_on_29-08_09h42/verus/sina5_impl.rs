use vstd::prelude::*;

verus!{

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut i = 0;
    /* code modified by LLM (iteration 5): moved arithmetic bounds assertion outside proof block to use precondition */
    assert(N < 1000);
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == 2 * N + 1,
        decreases N - i,
    {
        a[i as usize] = (2 * N + 1) as i32;
        i = i + 1;
    }
    // impl-end
}
// </vc-code>

}

fn main() {}