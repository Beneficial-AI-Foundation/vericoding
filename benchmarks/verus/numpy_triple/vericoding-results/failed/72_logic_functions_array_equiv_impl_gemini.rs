// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_equiv(a1: Vec<f32>, a2: Vec<f32>) -> (result: bool)
    requires a1.len() == a2.len(),
    ensures result == (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Changed spec vector indexing from v@[i] to v[i] to fix compilation error. */
    let mut i: usize = 0;
    while i < a1.len()
        invariant
            a1.len() == a2.len(),
            forall|j: int| 0 <= j < (i as int) ==> a1[j] == a2[j]
        decreases a1.len() - i
    {
        if a1[i] != a2[i] {
            assert_by(! (forall|k: int| 0 <= k < a1.len() ==> a1[k] == a2[k]), {});
            return false;
        }
        assert(a1[i as int] == a2[i as int]);
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}