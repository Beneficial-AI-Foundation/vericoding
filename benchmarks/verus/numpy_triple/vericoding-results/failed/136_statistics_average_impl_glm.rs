// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper to prove array bounds */
proof fn prove_a_index_in_bounds(i: usize, a_len: usize, w_len: usize)
    requires
        i < w_len,
        a_len == w_len,
    ensures
        i < a_len
{
    assert(a_len == w_len);
    assert(i < w_len);
    assert(i < a_len);
}
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
/* code modified by LLM (iteration 5): used integer counts and explicit proofs for array bounds */
{
    match weights {
        None => {
            let mut sum: f32 = 0.0;
            let mut count: usize = 0;
            for i in 0..a.len() {
                sum += a[i];
                count += 1;
            }
            // Since a.len() > 0 (from precondition), count must be > 0
            assert(count > 0);
            sum / (count as f32)
        }
        Some(w) => {
            // Explicitly establish that a.len() == w.len() from the precondition
            proof {
                assert(a.len() == w.len());
            }
            
            let mut weighted_sum: f32 = 0.0;
            let mut total_weight: f32 = 0.0;
            
            for i in 0..w.len() {
                // Prove that i is in bounds for a
                proof {
                    prove_a_index_in_bounds(i, a.len(), w.len());
                }
                // Now we can safely access a[i] and w[i]
                weighted_sum += a[i] * w[i];
                total_weight += w[i];
            }
            
            // Handle case where total_weight is 0
            if total_weight == 0.0 {
                // If all weights are 0, return simple average
                let mut sum: f32 = 0.0;
                let mut count: usize = 0;
                for i in 0..a.len() {
                    sum += a[i];
                    count += 1;
                }
                // Since a.len() > 0 (from precondition), count must be > 0
                assert(count > 0);
                sum / (count as f32)
            } else {
                weighted_sum / total_weight
            }
        }
    }
}
// </vc-code>

}
fn main() {}