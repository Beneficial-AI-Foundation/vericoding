// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn evaluate_laguerre_polynomial(c: Seq<f32>, x: f32) -> f32;

spec fn evaluate_polynomial(coeffs: Seq<f32>, x: f32) -> f32;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed invariant syntax - removed parentheses and added proper ghost variable handling */

exec spec fn evaluate_polynomial(coeffs: Seq<f32>, x: f32) -> f32 {
    decreases coeffs.len();
    if coeffs.len() == 0 {
        0.0
    } else {
        coeffs[0] + x * evaluate_polynomial(coeffs.subrange(1, coeffs.len() as int), x)
    }
}

spec fn convert_laguerre_to_polynomial(c: Seq<f32>) -> (result: Seq<f32>)
    decreases c.len()
{
    if c.len() == 0 {
        Seq::empty()
    } else if c.len() == 1 {
        c
    } else {
        let n = c.len();
        let prev = convert_laguerre_to_polynomial(c.subrange(0, n - 1));
        let last = c[n - 1];
        
        // Transform Laguerre coefficients to polynomial coefficients
        let mut new_coeffs = Seq::new(n, |i| 
            if i == 0 {
                last
            } else if i == 1 {
                prev[i] - last
            } else {
                prev[i] - prev[i - 1]
            }
        );
        new_coeffs
    }
}

proof fn laguerre_identity_lemma(c: Seq<f32>, x: f32)
    ensures evaluate_polynomial(convert_laguerre_to_polynomial(c), x) == evaluate_laguerre_polynomial(c, x)
    decreases c.len()
{
    if c.len() == 0 {
    } else if c.len() == 1 {
    } else {
        let prev = c.subrange(0, c.len() - 1);
        laguerre_identity_lemma(prev, x);
        // Main identity proof
        assert(evaluate_laguerre_polynomial(c, x) == evaluate_laguerre_polynomial(prev, x) - x * evaluate_polynomial(convert_laguerre_to_polynomial(prev), x));
    }
}
// </vc-helpers>

// <vc-spec>
fn lag2poly(c: Vec<f32>) -> (result: Vec<f32>)
    requires c.len() > 0,
    ensures
        result.len() == c.len(),

        forall|x: f32| evaluate_polynomial(result@, x) == evaluate_laguerre_polynomial(c@, x),

        c.len() == 1 ==> result@ == c@,

        c.len() > 0 ==> evaluate_polynomial(result@, 0.0) == evaluate_laguerre_polynomial(c@, 0.0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Simplified implementation using recursive helper function */
{
    let mut result = Vec::<f32>::new();
    let n = c.len();
    
    let coeffs_seq = convert_laguerre_to_polynomial(c@);
    
    let mut i: usize = 0;
    while i < n {
        invariant 0 <= i && i <= n;
        invariant result.len() == i;
        invariant forall|j: int| 0 <= j && j < i ==> result[j] == coeffs_seq[j];
        {
            result.push(coeffs_seq[i]);
            i += 1;
        }
    }
    
    proof {
        laguerre_identity_lemma(c@, 0.0);
        assert(evaluate_polynomial(result@, 0.0) == evaluate_laguerre_polynomial(c@, 0.0));
    }
    
    result
}
// </vc-code>

}
fn main() {}