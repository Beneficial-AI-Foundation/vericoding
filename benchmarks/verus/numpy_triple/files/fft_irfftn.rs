// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Complex number type for FFT operations */
pub struct Complex {
    /* Real part */
    pub re: f32,
    /* Imaginary part */
    pub im: f32,
}

impl Complex {
    pub closed spec fn new(re: f32, im: f32) -> Complex {
        Complex { re, im }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn irfftn(a: Vec<Complex>, n: u8) -> (result: Vec<f32>)
    requires 
        a.len() > 0,
        n > 0,
        a[0].im == 0.0f32,
    ensures
        result.len() == n as nat,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}