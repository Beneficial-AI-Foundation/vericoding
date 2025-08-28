use vstd::prelude::*;

verus!{

// <vc-helpers>
// No additional helper code needed for this fix.
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
		forall |k:int| 0 <= k < N ==> b[k] == N + 2,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    while i < N as usize
        invariant
            i <= N as usize,
            forall |k: usize| k < i ==> b@[k] == (N + 2) as i32,
        decreases
            N as usize - i,
    {
        b.set(i, N + 2);
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}