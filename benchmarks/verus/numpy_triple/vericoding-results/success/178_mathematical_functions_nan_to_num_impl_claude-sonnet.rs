// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added helper to check if f64 is NaN */
fn is_nan_f64(x: f64) -> bool {
    x != x
}

/* helper modified by LLM (iteration 4): added helper to check if f64 is infinite using comparison with large values */
fn is_infinite_f64(x: f64) -> bool {
    x > 1.0e308 || x < -1.0e308
}
// </vc-helpers>

// <vc-spec>
fn nan_to_num(x: Vec<f64>) -> (result: Vec<f64>)
    ensures 
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
        decreases x.len() - i
    {
        let val = if is_nan_f64(x[i]) {
            0.0
        } else if is_infinite_f64(x[i]) {
            if x[i] > 0.0 { 1.0e308 } else { -1.0e308 }
        } else {
            x[i]
        };
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}