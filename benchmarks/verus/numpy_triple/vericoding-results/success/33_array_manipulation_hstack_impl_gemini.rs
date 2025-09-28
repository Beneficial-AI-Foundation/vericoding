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
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == a[k],
        decreases a.len() - i
    {
        result.push(a[i]);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < b.len()
        invariant
            j <= b.len(),
            result.len() == a.len() + j,
            forall|k: int| 0 <= k < a.len() ==> result[k] == a[k],
            forall|k: int| 0 <= k < j ==> result[a.len() + k] == b[k],
        decreases b.len() - j
    {
        result.push(b[j]);
        j = j + 1;
    }

    result
}
// </vc-code>

}
fn main() {}