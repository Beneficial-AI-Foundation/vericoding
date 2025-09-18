// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use NaN property x != x to detect NaN */
spec fn is_nan_f32(x: f32) -> bool { x != x }
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
    /* code modified by LLM (iteration 5): compute product ignoring NaNs via iterative loop */
    let mut i: usize = 0;
    let mut prod: f32 = 1.0;
    while i < a.len()
        decreases a.len() - i
    {
        let x = a[i];
        if x != x {
            i += 1;
        } else {
            prod = prod * x;
            i += 1;
        }
    }
    prod
}
// </vc-code>

}
fn main() {}