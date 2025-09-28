// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn putmask(a: Vec<f32>, mask: Vec<bool>, values: Vec<f32>) -> (result: Vec<f32>)
    requires 
        a.len() == mask.len(),
        values.len() > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> (
            mask@[i] ==> exists|j: int| 0 <= j < values@.len() && result@[i] == values@[j]
        ),
        forall|i: int| 0 <= i < a@.len() ==> (
            mask@[i] ==> result@[i] == values@[(i as int) % (values@.len() as int)]
        ),
        forall|i: int| 0 <= i < a@.len() ==> (
            !mask@[i] ==> result@[i] == a@[i]
        ),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            a.len() == mask.len(),
            values.len() > 0,
            forall|j: int| 0 <= j < i ==> (
                mask@[j] ==> exists|k: int| 0 <= k < values@.len() && result@[j] == values@[k]
            ),
            forall|j: int| 0 <= j < i ==> (
                mask@[j] ==> result@[j] == values@[(j as int) % (values@.len() as int)]
            ),
            forall|j: int| 0 <= j < i ==> (
                !mask@[j] ==> result@[j] == a@[j]
            ),
        decreases a.len() - i
    {
        if mask[i] {
            let idx = (i as usize) % values.len();
            result.push(values[idx]);
        } else {
            result.push(a[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}