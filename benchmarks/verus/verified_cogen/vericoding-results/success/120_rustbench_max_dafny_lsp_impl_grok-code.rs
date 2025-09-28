// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added spec fn and lemma for verification */
spec fn is_max_at(a: Seq<i32>, x: int) -> bool {
    (0 <= x < a.len()) &&
        forall|k: int| 0 <= k < a.len() ==>
            a[k] <= a[x]
}

proof fn lemma_is_max_at(a: Seq<i32>, x: int)
    requires
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x],
    ensures
        is_max_at(a, x)
{
    assert forall|k: int| 0 <= k < a.len() implies a[k] <= a[x] by {
        // tautology from requires
    }
    assert(0 <= x < a.len());
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn max_dafny_lsp(a: &[i32]) -> (x: usize)
    requires
        a.len() > 0,
    ensures
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x as int],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Added decreases clause to while loop for verification */
{
    let ghost a_view = a.view();
    proof {
        assert(a_view.len() > 0);
    }
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            0 <= max_idx < i,
            forall|k: int| 0 <= k < i ==> a_view[k] <= a_view[max_idx as int],
        decreases (a.len() - i)
    {
        if a[i] > a[max_idx] {
            max_idx = i;
        }
        i += 1;
    }
    proof {
        lemma_is_max_at(a.view(), max_idx as int);
    }
    max_idx
}
// </vc-code>

}
fn main() {}