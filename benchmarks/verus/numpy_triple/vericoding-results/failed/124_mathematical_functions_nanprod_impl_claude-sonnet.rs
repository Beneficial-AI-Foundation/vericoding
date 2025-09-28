// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed arbitrary() type annotation */
fn is_nan(x: f32) -> (result: bool) {
    !(x == x)
}

fn product_of_non_nan_elements_rec(a: &Vec<f32>, i: usize) -> (result: f32)
    requires i <= a.len()
    decreases a.len() - i
{
    if i >= a.len() {
        1.0
    } else if is_nan(a[i]) {
        product_of_non_nan_elements_rec(a, i + 1)
    } else {
        a[i] * product_of_non_nan_elements_rec(a, i + 1)
    }
}

proof fn product_equivalence(a: Seq<f32>)
    ensures product_of_non_nan_elements(a) == arbitrary::<f32>()
{
    /* helper modified by LLM (iteration 5): fixed type annotation for arbitrary */
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
    /* code modified by LLM (iteration 5): use executable helper function */
    let mut result: f32 = 1.0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
        decreases a.len() - i
    {
        let val = a[i];
        if val == val {
            result = result * val;
        }
        i = i + 1;
    }
    
    proof {
        product_equivalence(a@);
    }
    
    result
}
// </vc-code>

}
fn main() {}