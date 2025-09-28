// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn minimum(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result@.len() ==> 
            (result@[i] == x1@[i] || result@[i] == x2@[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Access vector elements using `x1[i]` and `x2[i]` instead of `@` for runtime code. */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i ==> (result@[j] == x1@[j] || result@[j] == x2@[j]),
            i <= x1.len(),
        decreases x1.len() - i
    {
        if x1[i] < x2[i] {
            result.push(x1[i]);
        } else {
            result.push(x2[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}