// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed function signatures and added proper type annotations */
fn weighted_sum(a: Seq<f32>, weights: Seq<f32>) -> f32
    decreases a.len()
    requires a.len() == weights.len()
{
    if a.len() == 0 {
        0.0
    } else {
        a[a.len() - 1] * weights[a.len() - 1] + weighted_sum(a.subrange(0, a.len() - 1 as int), weights.subrange(0, weights.len() - 1 as int))
    }
}

fn sum_weights(weights: Seq<f32>) -> f32
    decreases weights.len()
{
    if weights.len() == 0 {
        0.0
    } else {
        weights[weights.len() - 1] + sum_weights(weights.subrange(0, weights.len() - 1 as int))
    }
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
/* code modified by LLM (iteration 5): Simplified implementation and fixed type casting */
{
    let a_seq = a@;
    match weights {
        Some(w) => {
            let w_seq = w@;
            let total_weight = sum_weights(w_seq);
            let weighted_total = weighted_sum(a_seq, w_seq);
            weighted_total / total_weight
        }
        None => {
            let mut sum = 0.0;
            let mut i: usize = 0;
            
            while i < a.len()
                invariant i <= a.len()
                invariant sum == a_seq.subrange(0, i as int).sum()
            {
                sum = sum + a[i];
                i = i + 1;
            }
            
            sum / (a.len() as f32)
        }
    }
}
// </vc-code>

}
fn main() {}