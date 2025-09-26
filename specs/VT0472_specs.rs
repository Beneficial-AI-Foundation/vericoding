// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn lagpow(c: Vec<f32>, pow: u8, maxpower: u8) -> (result: Vec<f32>)
    requires 
        pow > 0,
        pow <= maxpower,
        maxpower <= 16,
        c.len() > 0,
    ensures 
        result.len() == c.len(),
        pow == 1 ==> (forall|i: int| 0 <= i < result.len() ==> result[i] == c[i]),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}