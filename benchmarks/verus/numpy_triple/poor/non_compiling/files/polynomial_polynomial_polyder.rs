/* Differentiate a polynomial.

Returns the polynomial coefficients differentiated `m` times.
At each iteration the result is multiplied by `scl` (scaling factor).
The coefficients are from low to high degree, e.g., [1,2,3] represents 1 + 2*x + 3*x².

This specification handles the case where m ≤ n. When m > n, the derivative
would be the zero polynomial.

Specification: polyder computes the m-th derivative of a polynomial with scaling.

Mathematical properties: 
- d/dx(c[i] * x^i) = i * c[i] * x^(i-1)
- With scaling factor scl: d/d(scl*x)(c[i] * x^i) = scl * i * c[i] * x^(i-1)
- Taking m derivatives of x^i gives: i * (i-1) * ... * (i-m+1) * x^(i-m)

Each coefficient is multiplied by scl at each differentiation step,
resulting in multiplication by scl^m overall.

Sanity checks:
- Taking 0 derivatives returns the original polynomial
- The constant term (i=0) disappears after one derivative
- Higher order terms shift down by m positions */

use vstd::prelude::*;

verus! {
spec fn factorial_factor(original_idx: nat, m: nat) -> real
    decreases m
{
    if m == 0 {
        1.0
    } else {
        (original_idx - (m - 1)) as real * factorial_factor(original_idx, m - 1)
    }
}

spec fn scale_factor(scl: real, m: nat) -> real
    decreases m
{
    if m == 0 {
        1.0
    } else {
        scl * scale_factor(scl, m - 1)
    }
}

fn polyder(c: Vec<f32>, m: usize, scl: f32) -> (result: Vec<f32>)
    requires 
        m <= c.len(),
        c.len() > 0,
    ensures
        result.len() == c.len() - m,
        /* Special case: m = 0 returns original polynomial */
        (m == 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i] == c[i]),
        /* General case: m > 0 */
        (m > 0 ==> forall|i: int| 0 <= i < result.len() ==> {
            let original_idx = i + m;
            result[i] == c[original_idx] * factorial_factor(original_idx, m) as f32 * scale_factor(scl as real, m) as f32
        }),
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}