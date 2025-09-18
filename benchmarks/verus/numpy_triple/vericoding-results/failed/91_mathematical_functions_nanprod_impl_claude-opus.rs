// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed duplicate product_of_non_nan_elements definition */
spec fn is_nan(x: f32) -> bool {
    x != x
}

spec fn product_helper(a: Seq<f32>, i: nat) -> f32
    decreases a.len() - i
{
    if i >= a.len() {
        1.0
    } else if is_nan(a[i]) {
        product_helper(a, i + 1)
    } else {
        a[i] * product_helper(a, i + 1)
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
    /* code modified by LLM (iteration 5): Computing product using product_helper directly */
    let mut result: f32 = 1.0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result == product_helper(a@, 0) / product_helper(a@, i as nat),
    {
        if a[i] != a[i] {
            // NaN check
        } else {
            result = result * a[i];
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}