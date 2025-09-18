// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed return value naming for ensures clause */
fn is_nan(x: f64) -> bool {
    x != x
}

fn fix_value(x: f64) -> (result: f64)
    ensures true
{
    if is_nan(x) {
        0.0
    } else {
        x
    }
}
// </vc-helpers>

// <vc-spec>
fn numpy_fix(x: Vec<f64>) -> (result: Vec<f64>)
    ensures result.len() == x.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clause to fix compilation error */
    let mut result = Vec::with_capacity(x.len());
    let mut i = 0;
    while i < x.len()
        invariant
            result.len() == i,
            i <= x.len()
        decreases x.len() - i
    {
        result.push(fix_value(x[i]));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}