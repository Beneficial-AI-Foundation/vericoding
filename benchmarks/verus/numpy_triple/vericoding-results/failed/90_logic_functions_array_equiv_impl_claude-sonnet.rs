// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_equiv(a1: Vec<f32>, a2: Vec<f32>) -> (result: bool)
    requires a1.len() == a2.len(),
    ensures result == (forall|i: int| 0 <= i < a1@.len() ==> a1@[i] == a2@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added proper bounds check to ensure i < a2.len() and strengthened invariant */
    if a1.len() == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    while i < a1.len()
        invariant
            0 <= i <= a1.len(),
            a1.len() == a2.len(),
            forall|j: int| 0 <= j < i ==> a1@[j] == a2@[j],
        decreases a1.len() - i
    {
        if a1[i] != a2[i] {
            proof {
                let idx = i as int;
                assert(0 <= idx < a1@.len());
                assert(a1@[idx] != a2@[idx]);
                assert(!(forall|k: int| 0 <= k < a1@.len() ==> a1@[k] == a2@[k]));
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert(i == a1.len());
        assert(forall|j: int| 0 <= j < a1@.len() ==> a1@[j] == a2@[j]);
    }
    true
}
// </vc-code>

}
fn main() {}