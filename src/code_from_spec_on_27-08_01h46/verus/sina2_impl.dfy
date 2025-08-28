use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn in_bounds(x: i32) -> bool {
    x >= -2147483648 && x <= 2147483647
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut i = 0;
    while i < N
        invariant
            0 <= i <= N,
            N > 0,
            N < 1000,
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a@[k] == N + 1,
        decreases N - i,
    {
        a.set(i as usize, N + 1);
        i = i + 1;
    }
    // impl-end
}
// </vc-code>

}

fn main() {}