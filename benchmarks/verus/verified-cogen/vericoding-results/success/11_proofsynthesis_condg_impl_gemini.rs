// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,

	ensures
		forall |k:int| 0 <= k < N ==> a[k] == 0,
// </vc-spec>
// <vc-code>
{
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            a.len() == N,
            sum@ == old(sum)@,
            forall |k:int| 0 <= k < i ==> a@[k] == 0,
            forall |k:int| i <= k < N ==> a@[k] == old(a)@[k]
        decreases N - i
    {
        a[i as usize] = 0;
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}