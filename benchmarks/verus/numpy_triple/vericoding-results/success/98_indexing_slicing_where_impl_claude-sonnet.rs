// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn where_fn(condition: Vec<bool>, x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires 
        condition.len() == x.len(),
        x.len() == y.len(),
    ensures 
        result.len() == condition.len(),
        forall|i: int| 0 <= i < condition.len() ==> 
            result@[i] == if condition@[i] { x@[i] } else { y@[i] }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed invariant and bounds checking by ensuring i < vector lengths */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < condition.len()
        invariant
            i <= condition.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == if condition@[j] { x@[j] } else { y@[j] },
            condition.len() == x.len(),
            x.len() == y.len(),
        decreases condition.len() - i
    {
        let val = if condition[i] { x[i] } else { y[i] };
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}