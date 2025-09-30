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
    let mut result_vec = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == mask.len(),
            values.len() > 0,
            i <= a.len(),
            result_vec.len() == i,
            forall|k: int| 0 <= k < i ==> (mask@[k] ==> result_vec@[k] == values@[(k as int) % (values@.len() as int)]),
            forall|k: int| 0 <= k < i ==> (!mask@[k] ==> result_vec@[k] == a@[k]),
        decreases a.len() - i
    {
        if mask[i] {
            let index = i % values.len();
            result_vec.push(values[index]);
        } else {
            result_vec.push(a[i]);
        }
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}