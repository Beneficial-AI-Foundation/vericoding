// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures 
        exists|i: int| 0 <= i < a@.len() && result as int == a@[i],
        forall|i: int| 0 <= i < a@.len() ==> result as int <= a@[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): replace int with usize for executable code and adjust invariants */
    let mut current_min = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i as int <= a@.len(),
            exists|j: int| 0 <= j < i as int && current_min as int == a@[j],
            forall|j: int| 0 <= j < i as int ==> current_min as int <= a@[j],
        decreases a@.len() - i as int
    {
        if a[i] < current_min {
            current_min = a[i];
        }
        i += 1;
    }
    current_min
}
// </vc-code>


}
fn main() {}