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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}