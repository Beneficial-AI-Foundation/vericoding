// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_infinite(x: f64) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The original declaration `spec fn is_infinite(x: f64) -> bool;` is already in the preamble, so no helper function is needed here. This block is effectively empty. */

// </vc-helpers>

// <vc-spec>
fn isinf(x: Vec<f64>) -> (result: Vec<bool>)
    requires x.len() < usize::MAX,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> {
            result[i] == is_infinite(x@[i])
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error related to `int` index by casting to `usize` for vector access. */
{
    let mut result_vec: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i && i <= x.len(),
            result_vec.len() == i,
            // All elements processed so far satisfy the postcondition
            forall|j: int| 0 <= j < i ==> {
                result_vec@[j] == is_infinite(x@[j])
            },
            x.len() < usize::MAX,
    {
        // Verus does not have a native f64.is_infinite equivalent in spec, so we use the spec function `is_infinite`
        result_vec.push(is_infinite(x@[i as int]));
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}