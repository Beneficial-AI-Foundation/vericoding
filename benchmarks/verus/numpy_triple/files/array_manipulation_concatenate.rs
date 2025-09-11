// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn concatenate(a: Vec<f32>, b: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
        forall|j: int| 0 <= j < b.len() ==> result[a.len() + j] == b[j],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}