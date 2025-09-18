// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn poly2lag(pol: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == pol.len(),

        true,
// </vc-spec>
// <vc-code>
{
    let result = pol.clone();
    result
}
// </vc-code>

}
fn main() {}