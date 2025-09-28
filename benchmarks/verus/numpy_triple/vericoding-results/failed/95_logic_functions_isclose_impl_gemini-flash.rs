// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers are needed for this function. */

// </vc-helpers>

// <vc-spec>
fn isclose(a: Vec<f32>, b: Vec<f32>, rtol: f32, atol: f32, equal_nan: bool) -> (result: Vec<bool>)
    requires 
        a@.len() == b@.len(),
    ensures
        result@.len() == a@.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Correcting casting errors. `i` is now `int` and `len` is `usize`. Corrected Vec::set_len call as well. */
{
    let len: usize = a@.len() as usize;
    let mut result_vec = Vec::new();
    
    proof {
        result_vec.set_len(len as nat);
    }

    let mut i: int = 0;
    while (i as nat) < a@.len()
        invariant
            i >= 0,
            (i as nat) <= a@.len(),
            result_vec@.len() == a@.len(),
    {
        let val_a = a@.index(i as nat);
        let val_b = b@.index(i as nat);

        let current_result_val: bool;

        if equal_nan && val_a.is_nan() && val_b.is_nan() {
            current_result_val = true;
        } else if val_a.is_nan() || val_b.is_nan() {
            current_result_val = false;
        } else {
            let abs_diff = (val_a - val_b).abs();
            let b_abs = val_b.abs();
            let tol = rtol * b_abs + atol;
            current_result_val = abs_diff <= tol;
        }
        result_vec.set(i as nat, current_result_val); 
        i = i + 1;
    }

    result_vec
}
// </vc-code>


}
fn main() {}