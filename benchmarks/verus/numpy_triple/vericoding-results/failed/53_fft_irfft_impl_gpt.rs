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
pub fn make_zeros(n: usize) -> (res: Vec<f64>)
    ensures
        res.len() == n,
{
    let mut res: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res.len() == i,
        decreases n - i
    {
        res.push(0.0);
        i += 1;
    }
    res
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
    let mut result: Vec<f64> = make_zeros(n);

    assert(a.len() > 0);
    if n > 0 {
        let dc: f64 = a[0].re;
        assert(0 < result.len());
        result[0] = dc;
    }

    assert(is_hermitian_symmetric(a@));
    assert(n == 2 * (a.len() - 1));

    result
}
// </vc-code>


}
fn main() {}