// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn evaluate_laguerre_polynomial(c: Seq<f32>, x: f32) -> f32;

spec fn evaluate_polynomial(coeffs: Seq<f32>, x: f32) -> f32;
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): remove exec block and implement algorithm */
{
    let n = c.len();
    let mut result = vec![0.0; n];

    if n >= 1 {
        result[0] += c[0];
    }

    if n >= 2 {
        result[0] += c[1];
        result[1] += -c[1];
    }

    if n >= 3 {
        let mut poly_km1 = vec![1.0, -1.0];
        let mut poly_km2 = vec![1.0];

        for k in 2..n {
            let mut poly_k = vec![0.0; k+1];
            for i in 0..k+1 {
                let mut term = 0.0;
                if i < k {
                    term += (2*k-1) as f32 / k as f32 * poly_km1[i];
                }
                if i >= 1 {
                    term += -poly_km1[i-1] / k as f32;
                }
                if i < k-1 {
                    term += -((k-1) as f32) / k as f32 * poly_km2[i];
                }
                poly_k[i] = term;
            }

            for i in 0..k+1 {
                result[i] += c[k] * poly_k[i];
            }

            poly_km2 = poly_km1;
            poly_km1 = poly_k;
        }
    }

    result
}
// </vc-code>

}
fn main() {}