// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate definition causing compilation error */
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
    /* code modified by LLM (iteration 5): fixed base case initialization and multiplication logic */
    let mut result: f32 = 1.0;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result == product_of_non_nan_elements(a@.subrange(0, i as int))
        decreases a.len() - i
    {
        let val = a[i];
        if val == val {
            result = result * val;
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}