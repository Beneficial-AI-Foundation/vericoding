// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, N: u32)

		requires
			N > 0,
			old(a).len() == N,

		ensures
			forall |k:int| 0 <= k < N ==> a[k] % 2 == N % 2,
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = 0;
    while i < N
        invariant
            i <= N,
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k as int] % 2 == N % 2,
        decreases N - i
    {
        a.set(i as usize, if N % 2 == 0 { 0 } else { 1 });
        i += 1;
    }
}
// </vc-code>

}
fn main() {}