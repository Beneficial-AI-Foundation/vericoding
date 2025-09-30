// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_where(condition: Vec<bool>, x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires 
        condition@.len() == x@.len(),
        condition@.len() == y@.len(),
    ensures 
        result@.len() == condition@.len(),
        forall|i: int| 0 <= i < condition@.len() ==> 
            (condition@[i] ==> result@[i] == x@[i]) &&
            (!condition@[i] ==> result@[i] == y@[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): strengthened loop invariant to prove array index safety */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < condition.len()
        invariant
            x@.len() == condition@.len(),
            y@.len() == condition@.len(),
            0 <= i <= condition.len(),
            result@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> 
                (condition@[j] ==> result@[j] == x@[j]) &&
                (!condition@[j] ==> result@[j] == y@[j]),
        decreases condition.len() - i
    {
        if condition[i] {
            result.push(x[i]);
        } else {
            result.push(y[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}