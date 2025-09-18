// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed unused helpers, floor operation for i32 is identity */
// </vc-helpers>

// <vc-spec>
fn numpy_floor(x: Vec<i32>) -> (result: Vec<i32>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x[i],
        forall|i: int| 0 <= i < result.len() ==> x[i] < result[i] + 1,
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && x[i] <= x[j] ==> result[i] <= result[j],
        forall|i: int| 0 <= i < result.len() ==> result[i] == x[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clause for loop termination */
    let mut result: Vec<i32> = Vec::new();
    let mut idx = 0;
    
    while idx < x.len()
        invariant
            0 <= idx <= x.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < result.len() ==> result[i] <= x[i],
            forall|i: int| 0 <= i < result.len() ==> x[i] < result[i] + 1,
            forall|i: int| 0 <= i < result.len() ==> result[i] == x[i],
            forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && x[i] <= x[j] ==> result[i] <= result[j]
        decreases x.len() - idx
    {
        let floor_val = x[idx];
        result.push(floor_val);
        idx += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}