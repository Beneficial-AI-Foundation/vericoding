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
    /* code modified by LLM (iteration 2): added loop invariants for vector lengths and index bounds, and auto trigger for quantifier */
    let n = condition.len();
    let mut result = Vec::with_capacity(n);
    for i in 0..n
        invariant
            0 <= i <= n,
            condition.len() == n,
            x.len() == n,
            y.len() == n,
            result.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result@[j] == (if condition@[j] { x@[j] } else { y@[j] }),
        decreases n - i
    {
        if condition[i] {
            result.push(x[i]);
        } else {
            result.push(y[i]);
        }
    }
    result
}
// </vc-code>

}
fn main() {}