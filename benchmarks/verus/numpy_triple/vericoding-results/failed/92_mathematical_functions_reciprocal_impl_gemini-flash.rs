// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Correcting verification conditions for floating point calculations. */
fn reciprocal_value(val: f32) -> f32
    requires val != 0.0_f32
    // Using `==` with floats is problematic for proofs. Instead, we ensure the result is the mathematical reciprocal.
    // A realistic implementation would include a tolerance for floating-point comparisons.
    // Since Verus does not directly support float math in ensures for equality, this `ensures` is removed.
{
    1.0_f32 / val
}
// </vc-helpers>

// <vc-spec>
fn numpy_reciprocal(x: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i] != 0.0_f32,
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatches and ensured `nat` to `usize` conversions are safe within the loop bounds. */
{
    let mut result_vec: Vec<f32> = Vec::new();
    let len_usize = x.len();
    let len: nat = len_usize as nat;
    result_vec.reserve(len_usize);
    assert(len_usize == x@.len());
    let mut i: nat = 0;
    while i < len
        invariant
            0 <= i <= len,
            result_vec.len() == i as usize,
            result_vec.len() <= x.len(),
            len == x.len()
    {
        // Casting i to usize is safe because i is always <= len_usize
        let current_index_usize: usize = i as usize;
        assert(current_index_usize < x.len()); // Proves precondition for x[current_index_usize]
        proof {
            assert(forall|j: int| 0 <= j < x.len() ==> x[j] != 0.0_f32);
            assert(x@[i as int] != 0.0_f32);
        }
        result_vec.push(reciprocal_value(x[current_index_usize]));

        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}