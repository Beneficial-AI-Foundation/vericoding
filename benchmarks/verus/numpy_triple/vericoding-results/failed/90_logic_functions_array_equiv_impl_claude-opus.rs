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
    /* code modified by LLM (iteration 5): Simplified implementation removing unnecessary assertions and variable */
    let mut i: usize = 0;
    
    while i < a1.len()
        invariant
            0 <= i <= a1.len(),
            a1.len() == a2.len(),
            forall|j: int| 0 <= j < i ==> a1@[j] == a2@[j],
        decreases a1.len() - i
    {
        if a1[i] != a2[i] {
            return false;
        }
        i = i + 1;
    }
    
    true
}
// </vc-code>

}
fn main() {}