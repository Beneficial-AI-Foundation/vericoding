// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert Vec length to int */
spec fn len_as_int(v: &Vec<i32>) -> int { v.len() as int }
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,

	ensures
		forall |k:int| 0 <= k < N ==> a[k] == N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): set all elements to N using len snapshot and maintain invariants */
    let len = a.len();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            a.len() == len,
            forall |j:int| 0 <= j && j < (i as int) ==> a[j] == N,
        decreases len - i
    {
        a.set(i, N);
        i = i + 1;
    }
    proof {
        assert(i == len);
        assert(forall |k:int| 0 <= k && k < (i as int) ==> a[k] == N);
        assert(forall |k:int| 0 <= k && k < (len as int) ==> a[k] == N);
        assert((len as int) == N);
        assert(forall |k:int| 0 <= k && k < N ==> a[k] == N);
    }
}
// </vc-code>

}
fn main() {}