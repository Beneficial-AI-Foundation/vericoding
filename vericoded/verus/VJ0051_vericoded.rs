// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): strengthen postcondition to preserve all other indices and length */
fn set_at(a: &mut Vec<i32>, i: usize, val: i32)
    requires
        i < old(a).len(),
    ensures
        a.len() == old(a).len(),
        a[i as int] == val,
        forall |k:int| 0 <= k < old(a).len() && k != i as int ==> a[k] == old(a)[k]
{
    a[i] = val;
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,

	ensures
		forall |k:int| 0 <= k < N ==> a[k] == N + 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): safely fill a with N + 1 using a loop with strengthened invariants and overflow proof */
    assert(N > 0);
    assert(N < 1000);
    assert(1000 <= i32::MAX);
    assert(N < i32::MAX);
    let val: i32 = N + 1;

    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == old(a).len(),
            sum.len() == 1,
            forall |k:int| 0 <= k < i as int ==> a[k] == val,
        decreases (a.len() - i) as int
    {
        set_at(a, i, val);
        i = i + 1;
    }

    proof {
        assert(i == a.len());
        assert(a.len() == old(a).len());
        assert(old(a).len() == N);
        assert(a.len() == N);
    }

    assert(val == N + 1);
    assert(forall |k:int| 0 <= k < N ==> a[k] == N + 1);
}
// </vc-code>

}
fn main() {}