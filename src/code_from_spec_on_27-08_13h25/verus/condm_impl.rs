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
    let mut i: u32 = 0;
    while i < N
        invariant
            i <= N,
            a.len() == N as usize,
            forall |k: int| 0 <= k < i ==> a[k] % 2 == (N as int) % 2,
        decreases N - i
    {
        if a[i as usize] % 2 != (N as int) % 2 {
            a.set(i as usize, if N % 2 == 0 { 2 } else { 1 });
        }
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}