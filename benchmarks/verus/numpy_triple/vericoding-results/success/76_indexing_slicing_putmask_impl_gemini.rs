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
        forall|i: int| 0 <= i < a.len() ==> (
            mask[i] ==> exists|j: int| 0 <= j < values.len() && result[i] == values[j]
        ),
        forall|i: int| 0 <= i < a.len() ==> (
            mask[i] ==> result[i] == values[(i as int) % (values.len() as int)]
        ),
        forall|i: int| 0 <= i < a.len() ==> (
            !mask[i] ==> result[i] == a[i]
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to the while loop */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == mask.len(),
            values.len() > 0,
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> (mask[k] ==> result.view()[k] == values.view()[(k as int) % (values.len() as int)]),
            forall|k: int| 0 <= k < i ==> (!mask[k] ==> result.view()[k] == a.view()[k])
        decreases a.len() - i
    {
        if mask[i] {
            let j = i % values.len();
            result.push(values[j]);
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