// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added invariant `p.len() == n` to prove index safety */
fn multiply_by_x_minus_r(p: &Vec<f32>, r: f32) -> (result: Vec<f32>)
    requires
        p@.len() > 0,
        p@[p@.len() - 1] != 0.0f32,
    ensures
        result@.len() == p@.len() + 1,
        result@[result@.len() - 1] == p@[p@.len() - 1],
{
    let n = p.len();
    let mut result: Vec<f32> = Vec::new();

    // Constant term: c'_0 = -p[0] * r
    result.push(-p[0] * r);

    let mut j: usize = 1;
    while j < n
        invariant
            p.len() == n,
            1 <= j <= n,
            result.len() == j,
        decreases n - j
    {
        // Intermediate terms: c'_j = p_{j-1} - p_j * r
        result.push(p[j-1] - p[j] * r);
        j = j + 1;
    }
    
    // Leading term: c'_n = p_{n-1}
    result.push(p[n-1]);
    
    result
}
// </vc-helpers>

// <vc-spec>
fn hermfromroots(roots: Vec<f32>) -> (coef: Vec<f32>)
    ensures
        coef@.len() == roots@.len() + 1,
        roots@.len() > 0 ==> coef@[roots@.len() as int] != 0.0f32
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): retaining correct implementation */
    let mut coef = Vec::new();
    // The polynomial for zero roots is the constant 1.
    coef.push(1.0f32);

    let mut i: usize = 0;
    while i < roots.len()
        invariant
            // Loop counter bounds
            0 <= i <= roots.len(),
            // The number of coefficients is one more than the number of roots processed.
            coef@.len() == i as nat + 1,
            // The leading coefficient is non-zero.
            coef@[i as int] != 0.0f32,
        decreases roots.len() - i
    {
        // Multiply the current polynomial by (x - root)
        coef = multiply_by_x_minus_r(&coef, roots[i]);
        i = i + 1;
    }

    // Return the final list of coefficients.
    coef
}
// </vc-code>


}
fn main() {}