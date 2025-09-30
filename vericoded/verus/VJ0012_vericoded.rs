// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): provide simple range predicate used by invariants */
spec fn in_range(k: int, hi: int) -> bool { 0 <= k && k < hi }

/* helper modified by LLM (iteration 3): lemma showing range monotonicity */
proof fn range_mono(k: int, i: int, j: int)
    requires
        0 <= k,
        k < i,
        i <= j,
    ensures
        0 <= k,
        k < j
{ }

/* helper modified by LLM (iteration 3): lemma relating usize order to int order */
proof fn usize_to_int_le(u: usize, v: usize)
    requires
        u <= v,
    ensures
        (u as int) <= (v as int)
{ }
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
    /* code modified by LLM (iteration 3): remove unsupported &mut pattern and zero out all elements with stable length invariant */
    let n: usize = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a.len(),
            i <= n,
            forall |k:int| 0 <= k && k < i as int ==> a@[k] == 0,
        decreases n as int - i as int
    {
        a[i] = 0;
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}