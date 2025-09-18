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
{
    /* code modified by LLM (iteration 5): remove use of int type in non-ghost code */
    let n = c.len();
    let mut laguerre: Vec<Vec<f32>> = Vec::new();
    if n >= 1 {
        laguerre.push(vec![1.0]);
    }
    if n >= 2 {
        laguerre.push(vec![1.0, -1.0]);
    }
    for i in 2..n {
        let k1 = (2 * i - 1) as f32;
        let k2 = (i - 1) as f32;
        let l1 = &laguerre[i - 1];
        let l2 = &laguerre[i - 2];
        let mut l_i = vec![0.0; i + 1];
        l_i[0] = k1 * l1[0] - k2 * l2[0];
        for j in 1..i {
            l_i[j] = k1 * l1[j] - l1[j - 1];
            if j <= i - 2 {
                l_i[j] -= k2 * l2[j];
            }
        }
        l_i[i] = -l1[i - 1];
        laguerre.push(l_i);
    }
    let mut result = vec![0.0; n];
    for i in 0..n {
        for j in 0..(i+1) {
            result[j] += c[i] * laguerre[i][j];
        }
    }
    result
}
// </vc-code>

}
fn main() {}