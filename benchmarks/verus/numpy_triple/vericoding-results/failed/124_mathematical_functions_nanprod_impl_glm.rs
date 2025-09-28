// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_nan(x: f32) -> bool {
    x != x
}

/* helper modified by LLM (iteration 3): removed import and replaced spec_mul with * */
spec fn product_of_non_nan_elements_impl(a: Seq<f32>) -> f32 {
    if a.len() == 0 {
        1.0
    } else {
        let head = a[0];
        let tail = a.drop_first();
        if is_nan(head) {
            product_of_non_nan_elements_impl(tail)
        } else {
            head * product_of_non_nan_elements_impl(tail)
        }
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
    /* code modified by LLM (iteration 3): no changes needed */
    let mut product = 1.0;
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            product == product_of_non_nan_elements_impl(a@.subrange(0, i as int)),
        decreases a.len() - i
    {
        if !a[i].is_nan() {
            product = product * a[i];
        }
        i = i + 1;
    }
    product
}
// </vc-code>

}
fn main() {}