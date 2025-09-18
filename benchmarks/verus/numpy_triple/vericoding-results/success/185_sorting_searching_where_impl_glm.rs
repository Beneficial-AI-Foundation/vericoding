// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_where(condition: Vec<bool>, x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires 
        condition.len() == x.len(),
        condition.len() == y.len(),
    ensures 
        result.len() == condition.len(),
        forall|i: int| 0 <= i < condition.len() ==> 
            (condition[i] ==> result[i] == x[i]) &&
            (!condition[i] ==> result[i] == y[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added length invariants to fix indexing errors */
    let mut result = Vec::new();
    let n = condition.len();
    for i in 0..n
        invariant 
            0 <= i <= n,
            result.len() == i,
            condition.len() == n,
            x.len() == n,
            y.len() == n,
            forall|j: int| 0 <= j < i ==> 
                (condition[j] ==> result[j] == x[j]) && 
                (!condition[j] ==> result[j] == y[j])
    {
        let val = if condition[i] { x[i] } else { y[i] };
        result.push(val);
    }
    result
}
// </vc-code>

}
fn main() {}