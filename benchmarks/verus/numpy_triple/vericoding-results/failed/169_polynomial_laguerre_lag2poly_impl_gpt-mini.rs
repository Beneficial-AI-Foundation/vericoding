// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn evaluate_laguerre_polynomial(c: Seq<f32>, x: f32) -> f32;

spec fn evaluate_polynomial(coeffs: Seq<f32>, x: f32) -> f32;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): factorial without casting usize to f32 */
fn factorial(n: usize) -> f32 {
    let mut acc: f32 = 1.0;
    let mut k: usize = 1;
    let mut kf: f32 = 1.0;
    while k <= n
        invariant
            k >= 1,
            k <= n + 1,
        decreases n + 1 - k
    {
        acc = acc * kf;
        k = k + 1;
        kf = kf + 1.0;
    }
    acc
}

/* helper modified by LLM (iteration 5): pow_f32 using usize loop and decreases */
fn pow_f32(x: f32, k: usize) -> f32 {
    let mut acc: f32 = 1.0;
    let mut i: usize = 0;
    while i < k
        invariant
            i <= k,
        decreases k - i
    {
        acc = acc * x;
        i = i + 1;
    }
    acc
}

/* helper modified by LLM (iteration 5): binomial coefficient via factorial, requires k <= n */
fn binom(n: usize, k: usize) -> f32
    requires
        k <= n,
{
    factorial(n) / (factorial(k) * factorial(n - k))
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
    /* code modified by LLM (iteration 5): convert Laguerre coefficients to polynomial coefficients using helpers without casting */
    let n = c.len();
    let mut result: Vec<f32> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            result.len() == j,
            j <= n,
        decreases n - j
    {
        let mut s: f32 = 0.0;
        let mut i: usize = j;
        while i < n
            invariant
                j <= i,
                i <= n,
            decreases n - i
        {
            let sign: f32 = if j % 2 == 0 { 1.0 } else { -1.0 };
            let coeff: f32 = sign * binom(i, j) / factorial(j);
            s = s + c[i] * coeff;
            i = i + 1;
        }
        result.push(s);
        j = j + 1;
    }
    result
}

// </vc-code>

}
fn main() {}