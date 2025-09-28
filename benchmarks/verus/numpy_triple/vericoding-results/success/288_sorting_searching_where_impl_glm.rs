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
{
            /* code modified by LLM (iteration 3): added explicit length equalities in invariant */
            let n = condition.len();
            let mut result = Vec::new();
            for i in 0..n
                invariant
                    result@.len() == i,
                    i <= n,
                    condition@.len() == n,
                    x@.len() == n,
                    y@.len() == n,
                    forall|k: int| 0 <= k < i ==> 
                        (condition@[k] ==> result@[k] == x@[k]) &&
                        (!condition@[k] ==> result@[k] == y@[k])
            {
                let val = if condition[i] { x[i] } else { y[i] };
                result.push(val);
            }
            result
        }
// </vc-code>

}
fn main() {}