// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): safe float division returning 0.0 on zero divisor */
fn safe_div(x: f32, y: f32) -> f32 { if y == 0.0 { 0.0 } else { x / y } }
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
{
    /* code modified by LLM (iteration 5): compute weighted or unweighted average without loop invariants to fix parsing error */
    match weights {
        Some(w) => {
            let n = a.len();
            let mut i: usize = 0;
            let mut weighted_sum: f32 = 0.0;
            let mut total_weight: f32 = 0.0;
            while i < n {
                let wi = w[i];
                let ai = a[i];
                weighted_sum = weighted_sum + ai * wi;
                total_weight = total_weight + wi;
                i = i + 1;
            }
            safe_div(weighted_sum, total_weight)
        }
        None => {
            let n = a.len();
            let mut i: usize = 0;
            let mut sum: f32 = 0.0;
            let mut count: f32 = 0.0;
            while i < n {
                sum = sum + a[i];
                count = count + 1.0;
                i = i + 1;
            }
            safe_div(sum, count)
        }
    }
}
// </vc-code>

}
fn main() {}