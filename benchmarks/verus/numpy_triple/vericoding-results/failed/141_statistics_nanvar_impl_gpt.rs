// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): NaN predicate without std is_nan */
fn is_nan_f32(x: f32) -> f32 { (x != x) as i32 as f32 }

/* helper modified by LLM (iteration 5): square of a float */
fn square_f32(x: f32) -> f32 { x * x }

/* helper modified by LLM (iteration 5): safe division returning NaN via 0.0/0.0 when denominator is zero */
fn nan_if_zero(numer: f32, denom: f32) -> f32 { if denom == 0.0 { 0.0_f32 / 0.0_f32 } else { numer / denom } }

/* helper modified by LLM (iteration 5): convert usize to f32 by iterative addition */
fn usize_to_f32(n: usize) -> f32 {
    let mut i: usize = 0;
    let mut acc: f32 = 0.0;
    while i < n {
        acc = acc + 1.0;
        i = i + 1;
    }
    acc
}
// </vc-helpers>

// <vc-spec>
fn nanvar(a: Vec<f32>, ddof: usize) -> (result: f32)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement NaN-aware variance without using unsupported f32::NAN constant */
    let n = a.len();
    let mut i: usize = 0;
    let mut count_f: f32 = 0.0;
    let mut sum: f32 = 0.0;

    while i < n {
        let v = a[i];
        if !(v != v) {
            sum = sum + v;
            count_f = count_f + 1.0;
        }
        i = i + 1;
    }

    let mean: f32 = nan_if_zero(sum, count_f);

    let mut i2: usize = 0;
    let mut ssd: f32 = 0.0;
    let mut cnt2: usize = 0;
    while i2 < n {
        let v = a[i2];
        if !(v != v) {
            let d = v - mean;
            ssd = ssd + square_f32(d);
            cnt2 = cnt2 + 1;
        }
        i2 = i2 + 1;
    }

    let denom_u: usize = if cnt2 > ddof { cnt2 - ddof } else { 0 };
    let denom: f32 = usize_to_f32(denom_u);
    nan_if_zero(ssd, denom)
}
// </vc-code>

}
fn main() {}