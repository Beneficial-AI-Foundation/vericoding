// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed placeholder helper */
// </vc-helpers>

// <vc-spec>
fn average(a: Vec<f32>, weights: Option<Vec<f32>>) -> (result: f32)
    requires 
        a.len() > 0,
        match weights {
            Some(w) => w.len() == a.len(),
            None => true,
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error in `assert for_all` by adding `()` after it */
{
    let len = a.len();
    let mut sum: f32 = 0.0;
    let mut weight_sum: f32 = 0.0;

    match weights {
        Some(w) => {
            assert (for_all |i: int| (0 <= i && i < len) ==> w[i] >= 0.0) by {
                // This property must hold for weighted average to be meaningful
            };
            assert (for_all |i: int| (0 <= i && i < len) ==> w[i].is_finite()) by {
                // All weights must be finite
            };

            let mut i: int = 0;
            while i < len
                invariant
                    0 <= i <= len,
                    sum.is_finite(),
                    weight_sum.is_finite(),
                    sum >= 0.0,
                    weight_sum >= 0.0,
                 decreases len - i
            {
                let val = a[i];
                let weight = w[i];
                if weight > 0.0 {
                    sum = sum + val * weight;
                    weight_sum = weight_sum + weight;
                }
                i = i + 1;
            }
            if weight_sum > 0.0 {
                sum / weight_sum
            } else {
                // If all weights are zero, effectively unweighted average
                let mut unweighted_sum: f32 = 0.0;
                let mut j: int = 0;
                while j < len
                    invariant
                        0 <= j <= len,
                        unweighted_sum.is_finite(),
                    decreases len - j
                {
                    unweighted_sum = unweighted_sum + a[j];
                    j = j + 1;
                }
                unweighted_sum / len as f32
            }
        }
        None => {
            let mut i: int = 0;
            while i < len
                invariant
                    0 <= i <= len,
                    sum.is_finite(),
                decreases len - i
            {
                sum = sum + a[i];
                i = i + 1;
            }
            sum / len as f32
        }
    }
}
// </vc-code>

}
fn main() {}