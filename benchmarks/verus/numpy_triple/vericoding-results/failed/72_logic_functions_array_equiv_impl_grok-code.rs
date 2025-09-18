// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed for this fix */

// </vc-helpers>

// <vc-spec>
fn array_equiv(a1: Vec<f32>, a2: Vec<f32>) -> (result: bool)
    requires a1.len() == a2.len(),
    ensures result == (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): corrected the order of invariant and decreases in the while loop */
    let mut i: usize = 0;
    let len = a1.len();
    
    while i < len
        invariant 0 <= i <= len
        invariant forall |j: int| 0 <= j < i ==> a1[j] == a2[j]
        decreases len - i
    {
        if a1[i] != a2[i] {
            return false;
        }
        i += 1;
    }
    
    true
}
// </vc-code>

}
fn main() {}