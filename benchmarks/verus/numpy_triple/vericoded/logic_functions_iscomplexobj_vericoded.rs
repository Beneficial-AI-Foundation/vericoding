// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Complex number with real and imaginary parts */
#[derive(PartialEq, Structural)]
pub struct Complex {
    pub re: i32,
    pub im: i32,
}
// </vc-preamble>

// <vc-helpers>
fn always_true() -> (result: bool)
    ensures
        result == true,
{
    true
}
// </vc-helpers>

// <vc-spec>
fn iscomplexobj(x: Vec<Complex>) -> (result: bool)
    ensures 
        result == true
// </vc-spec>
// <vc-code>
{
    true
}
// </vc-code>


}
fn main() {}