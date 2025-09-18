// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
use std::primitive::f32;

/* helper modified by LLM (iteration 4): unchanged from previous */
fn filter_finite(vs: &Vec<f32>) -> Vec<f32> {
    let mut result = Vec::new();
    for v in vs {
        if v.is_finite() {
            result.push(*v);
        }
    }
    result
}

/* helper modified by LLM (iteration 4): unchanged from previous */
fn compute_sum(vs: &Vec<f32>) -> f32 {
    let mut result = 0.0;
    for v in vs {
        result += *v;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn nanvar(a: Vec<f32>, ddof: usize) -> (result: f32)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed compilation error by replacing usize to f32 casts with incremental computation */
    let filtered = filter_finite(&a);
    let mut n_f = 0.0;
    for _ in &filtered {
        n_f += 1.0;
    }
    if n_f == 0.0 {
        return 0.0;
    }
    let mu = compute_sum(&filtered) / n_f;
    let mut sum_sq = 0.0;
    for v in &filtered {
        let diff = v - mu;
        sum_sq += diff * diff;
    }
    let mut ddof_f = 0.0;
    for _ in 0..ddof {
        ddof_f += 1.0;
    }
    let denom = n_f - ddof_f;
    if denom <= 0.0 {
        return f32::NAN;
    }
    sum_sq / denom
}
// </vc-code>

}
fn main() {}