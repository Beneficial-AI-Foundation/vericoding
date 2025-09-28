// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hstack(a: Vec<f32>, b: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
        forall|j: int| 0 <= j < b.len() ==> result[a.len() + j] == b[j]
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    for i in 0..a.len()
        invariant
            result@ == a@.take(i as int),
            result.len() == i
    {
        result.push(a[i]);
    }
    for j in 0..b.len()
        invariant
            result@ == a@ + b@.take(j as int),
            result.len() == a.len() + j
    {
        result.push(b[j]);
    }
    result
}
// </vc-code>

}
fn main() {}