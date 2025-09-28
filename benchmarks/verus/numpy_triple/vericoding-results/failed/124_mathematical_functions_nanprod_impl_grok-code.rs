// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn product_of_non_nan_elements(a: Seq<f32>) -> f32
decreases a.len()
{
    if a.len() == 0 {
        1.0
    } else if a[0].is_nan() {
        product_of_non_nan_elements(a.drop(1))
    } else {
        a[0] * product_of_non_nan_elements(a.drop(1))
    }
}
// </vc-helpers>

// <vc-spec>
spec fn product_of_non_nan_elements(a: Seq<f32>) -> f32 {
    arbitrary()
}

fn nanprod(a: Vec<f32>) -> (result: f32)
    ensures result == product_of_non_nan_elements(a@)
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    let mut prod = 1.0;
    while i < a.len()
        invariant
            i <= a.len(),
            prod == product_of_non_nan_elements(a@.take(i as int))
        decreases a.len() - i
    {
        if !a[i].is_nan() {
            prod = prod * a[i];
        }
        i = i + 1;
    }
    prod
}
// </vc-code>

}
fn main() {}