// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn polyfromroots(roots: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result@.len() == roots@.len() + 1,
        result@[result@.len() - 1] == 1.0
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<f64> = Vec::new();
    let mut j: usize = 0;
    while j < roots.len()
        invariant
            j <= roots.len(),
            result@.len() == j as int,
            forall|k: int| 0 <= k && k < result@.len() ==> result@[k] == 0.0,
        decreases roots.len() - j
    {
        result.push(0.0);
        j += 1;
    }
    result.push(1.0);
    result
}
// </vc-code>


}
fn main() {}