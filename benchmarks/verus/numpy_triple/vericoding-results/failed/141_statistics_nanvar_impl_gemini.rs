// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no logical change */
fn is_not_nan(f: f32) -> bool { f == f }

/* helper modified by LLM (iteration 5): no logical change */
fn usize_to_f64_loop(u: usize) -> (res: f64) {
    let mut f: f64 = 0.0;
    let mut i: usize = 0;
    while i < u
        decreases u - i
    {
        f = f + 1.0;
        i = i + 1;
    }
    f
}
// </vc-helpers>

// <vc-spec>
fn nanvar(a: Vec<f32>, ddof: usize) -> (result: f32)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed while loop invariant syntax */
    let mut count: usize = 0;
    let mut sum: f64 = 0.0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            count <= i,
        decreases a.len() - i
    {
        let val = a[i];
        if is_not_nan(val) {
            count = count + 1;
            sum = sum + (val as f64);
        }
        i = i + 1;
    }

    if count <= ddof {
        return 0.0;
    }

    let count_f64 = usize_to_f64_loop(count);
    let mean = sum / count_f64;

    let mut sum_sq_diff: f64 = 0.0;
    i = 0;
    while i < a.len()
        invariant i <= a.len()
        decreases a.len() - i
    {
        let val = a[i];
        if is_not_nan(val) {
            let diff = (val as f64) - mean;
            sum_sq_diff = sum_sq_diff + diff * diff;
        }
        i = i + 1;
    }

    let denominator_usize = count - ddof;
    let denominator_f64 = usize_to_f64_loop(denominator_usize);
    
    (sum_sq_diff / denominator_f64) as f32
}
// </vc-code>

}
fn main() {}