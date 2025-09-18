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
            result[i] == if condition[i] { x[i] } else { y[i] }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to the while loop */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < condition.len()
        invariant
            i <= condition.len(),
            result.len() == i,
            condition.len() == x.len(),
            x.len() == y.len(),
            forall|j: int| 0 <= j < i as int ==> 
                result[j] == if condition[j] { x[j] } else { y[j] }
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