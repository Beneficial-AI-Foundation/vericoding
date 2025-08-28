use vstd::prelude::*;

verus!{

// <vc-helpers>
// No changes needed in helpers for this fix
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
		forall |k:int| 0 <= k < N ==> a[k] == N + 1,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            forall |k: int| 0 <= k < i ==> a@[k] == N + 1,
        decreases
            N - i
    {
        assert(i >= 0 && i < N);
        a.set(i as usize, (N + 1) as i32);
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}