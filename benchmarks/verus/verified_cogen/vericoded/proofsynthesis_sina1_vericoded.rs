// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix Seq::new length type to nat and keep constant-filled sequence constructor */
spec fn filled(len: nat, v: i32) -> Seq<i32> {
    Seq::new(len, |j: int| v)
}

/* helper modified by LLM (iteration 5): casting lemma for strict inequality usize -> int */
proof fn lemma_usize_lt_implies_int(i: usize, n: usize)
    requires
        i < n
    ensures
        0 <= (i as int),
        (i as int) < (n as int)
{
    assert(0 <= (i as int));
    assert((i as int) < (n as int));
}

/* helper modified by LLM (iteration 5): casting lemma for non-strict inequality usize -> int */
proof fn lemma_usize_le_implies_int(i: usize, n: usize)
    requires
        i <= n
    ensures
        (i as int) <= (n as int)
{
    assert((i as int) <= (n as int));
}
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
    /* code modified by LLM (iteration 5): fill vector a with N using a standard loop and maintain prefix invariant */
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            sum.len() == 1,
            i <= n,
            forall |k:int| 0 <= k < i as int ==> a@[k] == N
        decreases n - i
    {
        a[i] = N;
        i = i + 1;
    }
    proof {
        assert(forall |k:int| 0 <= k < n as int ==> a@[k] == N);
    }
}
// </vc-code>

}
fn main() {}