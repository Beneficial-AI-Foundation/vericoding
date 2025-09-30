// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebline(off: f32, scl: f32) -> (result: [f32; 2])
    ensures 
        result[0] == off,
        result[1] == scl
// </vc-spec>
// <vc-code>
{
    let r = [off, scl];
    r
}
// </vc-code>

}
fn main() {}