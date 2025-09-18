// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): empty helpers section */
// </vc-helpers>

// <vc-spec>
fn array_equiv(a1: Vec<f32>, a2: Vec<f32>) -> (result: bool)
    requires a1.len() == a2.len(),
    ensures result == (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop invariant and proof by establishing witness for existential */
    let mut i = 0;
    while i < a1.len()
        invariant
            0 <= i <= a1.len(),
            a1.len() == a2.len(),
            forall|j: int| 0 <= j < i ==> a1[j] == a2[j]
        decreases a1.len() - i
    {
        if a1[i] != a2[i] {
            proof {
                assert(a1[i as int] != a2[i as int]);
                assert(0 <= i < a1.len());
                assert(exists|k: int| 0 <= k < a1.len() && a1[k] != a2[k]) by {
                    assert(0 <= i as int < a1.len() && a1[i as int] != a2[i as int]);
                };
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert(i == a1.len());
        assert(forall|j: int| 0 <= j < a1.len() ==> a1[j] == a2[j]);
    }
    true
}
// </vc-code>

}
fn main() {}