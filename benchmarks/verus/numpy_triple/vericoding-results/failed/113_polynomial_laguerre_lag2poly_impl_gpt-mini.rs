// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn evaluate_laguerre_polynomial(c: Seq<f32>, x: f32) -> f32;

spec fn evaluate_polynomial(coeffs: Seq<f32>, x: f32) -> f32;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): factorial_f32: compute factorial as f32 iteratively with decreases */
fn factorial_f32(k: usize) -> f32 {
    let mut r: f32 = 1.0;
    let mut i: usize = 1;
    while i <= k decreases k + 1 - i {
        r = r * (i as f32);
        i += 1;
    }
    r
}

/* helper modified by LLM (iteration 5): binomial_f32: compute binomial coefficient as f32 using multiplicative formula with symmetry and decreases */
fn binomial_f32(n: usize, k: usize) -> f32 {
    if k > n {
        0.0
    } else {
        let mut kk = k;
        if kk > n - kk {
            kk = n - kk;
        }
        let mut res: f32 = 1.0;
        let mut i: usize = 1;
        while i <= kk decreases kk + 1 - i {
            res = res * ((n - kk + i) as f32) / (i as f32);
            i += 1;
        }
        res
    }
}

/* helper modified by LLM (iteration 5): sign_pow: (-1)^k as f32 */
fn sign_pow(k: usize) -> f32 {
    if k % 2 == 0 { 1.0 } else { -1.0 }
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
{
    /* code modified by LLM (iteration 5): compute polynomial coefficients from Laguerre coefficients with invariants and safe float arithmetic */
    let n = c.len();
    let mut result: Vec<f32> = Vec::new();
    let mut k: usize = 0;
    while k < n decreases n - k {
        invariant(k <= n);
        invariant(result.len() == k);
        let mut sum: f32 = 0.0;
        let mut i: usize = k;
        while i < n decreases n - i {
            invariant(i < n);
            invariant(i >= k);
            let coeff: f32 = c[i];
            let term: f32 = coeff * sign_pow(k) * (binomial_f32(i, k) / factorial_f32(k));
            sum = sum + term;
            i += 1;
        }
        result.push(sum);
        k += 1;
    }
    result
}
// </vc-code>

}
fn main() {}