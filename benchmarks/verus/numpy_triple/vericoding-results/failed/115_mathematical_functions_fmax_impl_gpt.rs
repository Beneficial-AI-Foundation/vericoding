// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_nan(f: f32) -> bool;

spec fn float_max(x: f32, y: f32) -> f32;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide executable helpers without redefining spec functions */
fn is_nan_exec(f: f32) -> (r: bool)
{
    let r0 = f != f;
    r0
}

/* helper modified by LLM (iteration 5): executable maximum with NaN handling; avoids using unsupported f32::NAN by returning one NaN input */
fn float_max_exec(x: f32, y: f32) -> (r: f32)
{
    let rx_nan = is_nan_exec(x);
    let ry_nan = is_nan_exec(y);
    if rx_nan && ry_nan {
        x
    } else if rx_nan {
        y
    } else if ry_nan {
        x
    } else if x >= y {
        x
    } else {
        y
    }
}
// </vc-helpers>

// <vc-spec>
fn fmax(x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires x@.len() == y@.len(),
    ensures 
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            /* Core NaN handling behavior */
            (!is_nan(x@[i]) && !is_nan(y@[i])) ==> 
                (result@[i] == float_max(x@[i], y@[i])) &&
            (is_nan(x@[i]) && !is_nan(y@[i])) ==> 
                (result@[i] == y@[i]) &&
            (!is_nan(x@[i]) && is_nan(y@[i])) ==> 
                (result@[i] == x@[i]) &&
            (is_nan(x@[i]) && is_nan(y@[i])) ==> 
                is_nan(result@[i]) &&
            /* Mathematical properties for non-NaN cases */
            (!is_nan(x@[i]) && !is_nan(y@[i])) ==> 
                (result@[i] == x@[i] || result@[i] == y@[i]) &&
            /* NaN preservation: result is NaN iff both inputs are NaN */
            is_nan(result@[i]) <==> (is_nan(x@[i]) && is_nan(y@[i]))
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute results with executable helpers; avoid unsupported constants */
    let n: usize = x.len();
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            x@.len() == n as int,
            y@.len() == n as int,
            result@.len() == i as int,
            i <= n,
            forall|j: int| 0 <= j < result@.len() ==> {
                ((!is_nan(x@[j]) && !is_nan(y@[j])) ==> (result@[j] == float_max(x@[j], y@[j]))) &&
                ((!is_nan(x@[j]) && !is_nan(y@[j])) ==> (result@[j] == x@[j] || result@[j] == y@[j])) &&
                ((is_nan(x@[j]) && !is_nan(y@[j])) ==> (result@[j] == y@[j])) &&
                ((!is_nan(x@[j]) && is_nan(y@[j])) ==> (result@[j] == x@[j])) &&
                ((is_nan(x@[j]) && is_nan(y@[j])) ==> is_nan(result@[j])) &&
                (is_nan(result@[j]) <==> (is_nan(x@[j]) && is_nan(y@[j])))
            },
        decreases n as int - i as int
    {
        let xi = x[i];
        let yi = y[i];
        let ri = float_max_exec(xi, yi);
        result.push(ri);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}