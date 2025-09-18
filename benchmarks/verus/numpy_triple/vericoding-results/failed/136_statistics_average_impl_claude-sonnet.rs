// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): converted usize to int before casting to f32 */
exec fn sum_f32(v: Vec<f32>) -> f32 {
    let mut sum = 0.0;
    for i in 0..v.len() {
        sum += v[i];
    }
    sum
}

exec fn weighted_sum(values: Vec<f32>, weights: Vec<f32>) -> f32 {
    let mut sum = 0.0;
    for i in 0..values.len() {
        sum += values[i] * weights[i];
    }
    sum
}

exec fn sum_weights(weights: Vec<f32>) -> f32 {
    let mut sum = 0.0;
    for i in 0..weights.len() {
        sum += weights[i];
    }
    sum
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
/* code modified by LLM (iteration 5): fixed cast by converting usize to int first then to f32 */
{
    match weights {
        Some(w) => {
            let weighted_total = weighted_sum(a, w);
            let weight_total = sum_weights(w);
            weighted_total / weight_total
        },
        None => {
            let total = sum_f32(a);
            let len_int = a.len() as int;
            let len_f32 = len_int as f32;
            total / len_f32
        }
    }
}
// </vc-code>

}
fn main() {}