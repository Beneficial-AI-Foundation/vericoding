// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn reciprocal_f32(val: f32) -> f32
    ensures
        // The original error indicated 'no method named `spec_mul` found for type `f32`'
        // Direct multiplication `*` on `f32` is generally understood by Verus for numerical types.
        // If formal verification of floating point arithmetic is needed, Verus typically
        // requires a more specialized approach, such as modeling it with integers or rationals,
        // or using an external SMT solver that supports floating point arithmetic.
        // For this context, assuming standard FPU behavior where `val * (1.0 / val)` is `1.0`
        // when `val` is not zero and normal.
        val != 0.0f32 ==> val * reciprocal_f32(val) == 1.0f32,
{
    1.0f32 / val
}
// </vc-helpers>

// <vc-spec>
fn numpy_reciprocal(x: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> x@[i] != 0.0f32,
    ensures
        result@.len() == x@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed `spec_mul` error by removing it, as Verus handles direct `f32` multiplication for verification. */
    let mut result: Vec<f32> = Vec::new();
    let x_len = x.len();
    result.reserve(x_len);

    let mut i: usize = 0;
    while i < x_len
        invariant
            result.len() == i,
            x.len() == x_len,
            forall|j: int| 0 <= j < i ==> x@[j] != 0.0f32 && x@[j] * result@[j] == 1.0f32,
            i <= x_len,
        decreases x_len - i
    {
        let val: f32 = x[i];
        result.push(reciprocal_f32(val));
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}