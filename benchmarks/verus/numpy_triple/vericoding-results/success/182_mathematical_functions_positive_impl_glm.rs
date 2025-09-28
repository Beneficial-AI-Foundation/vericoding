// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn positive(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x[i],
// </vc-spec>
// <vc-code>
{
    x
}
// </vc-code>

}
fn main() {}