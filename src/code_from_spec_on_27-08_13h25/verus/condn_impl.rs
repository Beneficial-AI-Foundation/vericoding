use vstd::prelude::*;

verus!{

// <vc-helpers>
// No updates needed for helpers in this case
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
    let mut i: usize = 0;
    while i < old(a).len()
        invariant
            i <= old(a).len(),
            forall |k: usize| 0 <= k < i ==> a@[k] <= N,
        decreases old(a).len() - i
    {
        if a[i] > N {
            a.set(i, N);
        }
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}