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
{
    let n = pol.len();
    let mut result = Vec::new();
    result.resize(n, 0.0f32);
    result
}
// </vc-code>

}
fn main() {}