// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nanvar(a: Vec<f32>, ddof: usize) -> (result: f32)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid integer to float casts by using loops to build float representations */
    let filtered: Vec<f32> = a.into_iter().filter(|x| *x == *x).collect();
    let n = filtered.len();
    if n <= ddof {
        return f32::NAN;
    }

    // Precompute ddof_float by a loop of ddof iterations.
    let mut ddof_float = 0.0f32;
    let mut j = 0;
    while j < ddof
        decreases ddof - j
    {
        ddof_float = ddof_float + 1.0f32;
        j = j + 1;
    }

    // Compute the sum and count (n as float) in one loop over filtered.
    let mut sum = 0.0f32;
    let mut count = 0.0f32;
    for x in &filtered {
        sum = sum + *x;
        count = count + 1.0f32;
    }

    let mean = sum / count;

    // Compute the sum of squared differences.
    let mut sum_sq = 0.0f32;
    for x in &filtered {
        let diff = *x - mean;
        sum_sq = sum_sq + diff * diff;
    }

    let denominator_float = count - ddof_float;
    sum_sq / denominator_float
}
// </vc-code>

}
fn main() {}