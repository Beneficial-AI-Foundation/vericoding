// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn square_f64(x: f64) -> f64;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed redundant `square_f64` helper. */

// </vc-helpers>

// <vc-spec>
fn numpy_square(x: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == square_f64(x[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed `uninterp spec` declaration to be global and fixed the implementation to account for the corrected spec function. */
{
    let mut result_vec: Vec<f64> = Vec::new();
    let mut i: usize = 0;

    while i < x.len()
        invariant
            i as int <= x.len() as int,
            result_vec.len() == i,
            forall|j: int| 0 <= j < i as int ==> result_vec[j as usize] == square_f64(x[j as usize]),
            x.len() == old(x.len()),
        decreases x.len() as nat - i as nat
    {
        result_vec.push(square_f64(x[i]));
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}