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
    /* code modified by LLM (iteration 5): moved precondition assertions outside loop to establish bounds before entering */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    
    proof {
        assert(condition.len() == x.len());
        assert(condition.len() == y.len());
    }
    
    while i < condition.len()
        invariant
            i <= condition.len(),
            result.len() == i,
            condition.len() == x.len(),
            condition.len() == y.len(),
            forall|j: int| 0 <= j < i ==> 
                (condition[j] ==> result[j] == x[j]) &&
                (!condition[j] ==> result[j] == y[j])
        decreases condition.len() - i
    {
        if condition[i] {
            result.push(x[i]);
        } else {
            result.push(y[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}