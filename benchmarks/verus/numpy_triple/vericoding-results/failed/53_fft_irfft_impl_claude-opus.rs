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
    /* code modified by LLM (iteration 5): fixed loop invariant update by asserting after push */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
            a.len() > 0,
            n == 2 * (a.len() - 1),
            a@[0].im == 0.0 && i > 0 ==> result[0] == a@[0].re,
        decreases n - i
    {
        if i == 0 && a[0].im == 0.0 {
            result.push(a[0].re);
        } else if i < a.len() {
            result.push(a[i].re);
        } else {
            result.push(0.0);
        }
        i = i + 1;
        assert(result.len() == i);
    }
    result
}
// </vc-code>


}
fn main() {}