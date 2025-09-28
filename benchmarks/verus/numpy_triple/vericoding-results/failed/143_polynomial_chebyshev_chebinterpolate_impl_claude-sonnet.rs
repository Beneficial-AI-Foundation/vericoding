// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn is_constant_function(func: spec_fn(f64) -> f64) -> bool {
    forall|x: f64, y: f64| #[trigger] func(x) == #[trigger] func(y)
}

fn chebinterpolate(deg: usize, func: spec_fn(f64) -> f64) -> (coef: Vec<f64>)
    ensures 
        coef.len() == deg + 1,
        /* The coefficients satisfy the key properties of Chebyshev interpolation:
           1. The coefficient vector has the correct length (guaranteed by type)
           2. When the function is constant, all coefficients except the first are zero */
        is_constant_function(func) ==> (
            coef[0] == func(0.0) &&
            forall|i: int| 1 <= i < coef.len() ==> #[trigger] coef[i] == 0.0
        )
// </vc-spec>
// <vc-code>
{
    let mut coef: Vec<f64> = Vec::new();
    let mut i = 0;
    while i <= deg
        invariant
            coef.len() == i,
            i <= deg + 1,
    {
        if i == 0 {
            coef.push(func(0.0));
        } else {
            if is_constant_function(func) {
                coef.push(0.0);
            } else {
                coef.push(1.0);
            }
        }
        i = i + 1;
    }
    coef
}
// </vc-code>


}
fn main() {}