// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq)]
pub struct Complex {
    pub real: f32,
    pub imag: f32,
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn hfft(a: Vec<Complex>, m: u8) -> (result: Vec<f32>)
    requires 
        m > 0,
        a.len() == m as nat + 1,
    ensures
        result.len() == 2 * m as nat,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}