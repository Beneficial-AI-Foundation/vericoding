// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn chebline_helper(off: f32, scl: f32) -> (result: [f32; 2])
    ensures
        result[0] == off,
        result[1] == scl
{
    [off, scl]
}
// </vc-helpers>

// <vc-spec>
fn chebline(off: f32, scl: f32) -> (result: [f32; 2])
    ensures 
        result[0] == off,
        result[1] == scl
// </vc-spec>
// <vc-code>
{
    chebline_helper(off, scl)
}
// </vc-code>

}
fn main() {}