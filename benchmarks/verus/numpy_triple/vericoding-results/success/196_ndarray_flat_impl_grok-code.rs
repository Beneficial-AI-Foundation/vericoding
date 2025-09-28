// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_flat(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<f32>::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j],
        decreases a.len() - i
    {
        result.push(a[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}