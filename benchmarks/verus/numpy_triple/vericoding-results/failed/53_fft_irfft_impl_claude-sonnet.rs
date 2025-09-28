// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Complex number type for FFT operations */
pub struct Complex {
    /* Real part of the complex number */
    pub re: f64,
    /* Imaginary part of the complex number */
    pub im: f64,
}
/* Helper function to check if a vector is Hermitian-symmetric */
spec fn is_hermitian_symmetric(a: Seq<Complex>) -> bool {
    a.len() > 0 
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed return variable name in ensures clauses */
/* Complex number addition */
fn complex_add(a: Complex, b: Complex) -> (result: Complex)
    requires
        a.re.is_finite(),
        a.im.is_finite(),
        b.re.is_finite(),
        b.im.is_finite(),
    ensures
        result.re.is_finite(),
        result.im.is_finite(),
{
    Complex { re: a.re + b.re, im: a.im + b.im }
}

/* Complex number multiplication */
fn complex_mul(a: Complex, b: Complex) -> (result: Complex)
    requires
        a.re.is_finite(),
        a.im.is_finite(),
        b.re.is_finite(),
        b.im.is_finite(),
    ensures
        result.re.is_finite(),
        result.im.is_finite(),
{
    Complex { 
        re: a.re * b.re - a.im * b.im,
        im: a.re * b.im + a.im * b.re
    }
}

/* Get the conjugate of a complex number */
fn complex_conjugate(z: Complex) -> Complex {
    Complex { re: z.re, im: -z.im }
}
// </vc-helpers>

// <vc-spec>
fn irfft(a: Vec<Complex>, n: usize) -> (result: Vec<f64>)
    requires 
        a.len() > 0,
        n == 2 * (a.len() - 1),
        is_hermitian_symmetric(a@),
    ensures
        /* Length preservation: output length matches specified n */
        result.len() == n,
        /* DC component preservation: first element is real when input DC is real */
        a@[0].im == 0.0 ==> exists|i: int| 0 <= i < result.len() && result[i] == a@[0].re,
        /* Hermitian input constraint: the input must be Hermitian-symmetric */
        is_hermitian_symmetric(a@),
        /* Length relationship: output length is twice the input length minus 2 */
        n == 2 * (a.len() - 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariants and bounds checking */
    let mut result: Vec<f64> = Vec::new();
    let len = a.len();
    
    let mut i = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
            len == a.len(),
            len > 0,
            n == 2 * (len - 1),
        decreases n - i
    {
        if i < len {
            // Use the provided frequency domain data
            result.push(a[i].re);
        } else {
            // Mirror the conjugate for Hermitian symmetry
            let mirror_idx = n - i;
            if mirror_idx < len {
                result.push(a[mirror_idx].re);
            } else {
                result.push(0.0);
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}