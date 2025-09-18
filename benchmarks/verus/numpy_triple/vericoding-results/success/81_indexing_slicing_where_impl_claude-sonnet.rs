// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed helper function as it's not needed for simple conditional selection */
// </vc-helpers>

// <vc-spec>
fn where_fn(condition: Vec<bool>, x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires 
        condition.len() == x.len(),
        x.len() == y.len(),
    ensures 
        result.len() == condition.len(),
        forall|i: int| 0 <= i < condition.len() ==> 
            result[i] == if condition[i] { x[i] } else { y[i] }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clause to fix verification error */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < condition.len()
        invariant
            0 <= i <= condition.len(),
            condition.len() == x.len(),
            x.len() == y.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == if condition[j] { x[j] } else { y[j] }
        decreases condition.len() - i
    {
        let value = if condition[i] { x[i] } else { y[i] };
        result.push(value);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}