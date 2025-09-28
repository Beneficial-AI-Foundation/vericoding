// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn isclose(a: Vec<f32>, b: Vec<f32>, rtol: f32, atol: f32, equal_nan: bool) -> (result: Vec<bool>)
    requires 
        a@.len() == b@.len(),
    ensures
        result@.len() == a@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified implementation without unsupported float operations */
    let mut result = Vec::new();
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            i == result.len(),
            result@.len() == i,
            a@.len() == b@.len(),
            a.len() == n,
            b.len() == n,
        decreases n - i
    {
        let a_val = a[i];
        let b_val = b[i];
        
        // Compute absolute difference
        let diff = if a_val >= b_val { a_val - b_val } else { b_val - a_val };
        
        // Compute absolute value of b
        let b_abs = if b_val >= 0.0 { b_val } else { -b_val };
        
        // Check if values are close
        let is_close = diff <= atol + rtol * b_abs;
        
        result.push(is_close);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}