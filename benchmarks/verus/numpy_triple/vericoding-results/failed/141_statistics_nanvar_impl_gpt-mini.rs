// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): is_nan for f32 */
fn is_nan_f32(x: f32) -> bool { x != x }
// </vc-helpers>

// <vc-spec>
fn nanvar(a: Vec<f32>, ddof: usize) -> (result: f32)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute nan-aware variance using two passes and index casts */
    let mut sum: f64 = 0.0;
    let mut n: usize = 0usize;
    let mut i: usize = 0usize;
    while i < a.len() invariant n <= i && i <= a.len() decreases a.len() - i {
        let x: f32 = a@.index(i as int);
        if !is_nan_f32(x) {
            sum += (x as f64);
            n += 1;
        }
        i += 1;
    }
    if n <= ddof {
        f32::NAN
    } else {
        let mean = sum / (n as f64);
        let mut ssd: f64 = 0.0;
        let mut j: usize = 0usize;
        while j < a.len() invariant j <= a.len() decreases a.len() - j {
            let x: f32 = a@.index(j as int);
            if !is_nan_f32(x) {
                let d: f64 = (x as f64) - mean;
                ssd += d * d;
            }
            j += 1;
        }
        let denom = (n - ddof) as f64;
        let res = (ssd / denom) as f32;
        res
    }
}
// </vc-code>

}
fn main() {}