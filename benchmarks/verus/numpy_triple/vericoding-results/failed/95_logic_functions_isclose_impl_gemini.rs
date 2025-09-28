// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [replace is_nan() with self-inequality check] */
exec fn isclose_element(a: f32, b: f32, rtol: f32, atol: f32, equal_nan: bool) -> (res: bool)
{
    let an = a != a;
    let bn = b != b;
    if an || bn {
        equal_nan && an && bn
    } else {
        (a - b).abs() <= atol + rtol * b.abs()
    }
}
// </vc-helpers>

// <vc-spec>
fn isclose(a: Vec<f32>, b: Vec<f32>, rtol: f32, atol: f32, equal_nan: bool) -> (result: Vec<bool>)
    requires 
        a@.len() == b@.len(),
    ensures
        result@.len() == a@.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [no change to logic, which depends on helper] */
{
    let len = a.len();
    let mut result = Vec::with_capacity(len);
    let mut i: usize = 0;
    while i < len
        invariant
            a@.len() == b@.len(),
            len == a@.len(),
            0 <= i <= len,
            result@.len() == i,
        decreases len - i
    {
        let close = isclose_element(a[i], b[i], rtol, atol, equal_nan);
        result.push(close);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}