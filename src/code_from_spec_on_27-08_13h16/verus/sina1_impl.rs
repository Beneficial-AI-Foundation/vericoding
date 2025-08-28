use vstd::prelude::*;

verus!{

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	// pre-conditions-start
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
	// pre-conditions-end
	// post-conditions-start
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            forall |k: usize| 0 <= k < i ==> a@[k as int] == N,
        decreases (N as usize) - i
    {
        a.set(i, N);
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}