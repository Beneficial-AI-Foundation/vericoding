use vstd::prelude::*;

verus!{

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut i = 0;
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] <= N,
        decreases N - i,
    {
        if a[i as usize] > N {
            a.set(i as usize, N);
        }
        i = i + 1;
    }
    // impl-end
}
// </vc-code>

}

fn main() {}