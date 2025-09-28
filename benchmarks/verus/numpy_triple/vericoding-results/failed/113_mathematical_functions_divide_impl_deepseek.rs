// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): fixed function signatures and return values */
fn is_finite_vec(v: Vec<f32>) -> bool
    ensures
        result == forall|i: int| 0 <= i < v.len() ==> (#[trigger] v@[i]).is_finite(),
{
    !exists|i: int| 0 <= i < v.len() && !v@[i].is_finite()
}

fn no_zeros(v: Vec<f32>) -> bool
    ensures
        result == forall|i: int| 0 <= i < v.len() ==> (#[trigger] v@[i]) != 0.0f32,
{
    !exists|i: int| 0 <= i < v.len() && v@[i] == 0.0f32
}

// </vc-helpers>

// <vc-spec>
fn numpy_divide(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added result variable declaration and fixed ensures clause */
    let len = x1.len();
    let mut result = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            result@.len() == i
    {
        let dividend = x1[i];
        let divisor = x2[i];
        let quotient = dividend / divisor;
        result.push(quotient);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}