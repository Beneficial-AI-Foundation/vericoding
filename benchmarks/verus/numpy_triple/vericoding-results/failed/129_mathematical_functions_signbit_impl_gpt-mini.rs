// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_negative(x: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate is_negative definition */
// </vc-helpers>

// <vc-spec>
fn signbit(x: Vec<f32>) -> (result: Vec<bool>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == is_negative(x[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement signbit by pushing x[i] < 0.0f32 for each element */
    let mut result: Vec<bool> = Vec::new();
    let mut i: int = 0;
    while i < x.len()
        invariant
            0 <= i,
            i <= x.len(),
            result.len() == i,
        decreases x.len() - i
    {
        result.push(x[i] < 0.0f32);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}