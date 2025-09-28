// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn poly2leg(pol: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == pol.len(),
// </vc-spec>
// <vc-code>
{/* code modified by LLM (iteration 3): Fixed compilation error by changing indexer to pol[i] and using usize for loop index */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < pol.len()
        invariant
            i <= pol.len(),
            result.len() == i,
        decreases pol.len() - i
    {
        result.push(pol[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}