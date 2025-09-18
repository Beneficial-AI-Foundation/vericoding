// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn mk_pair(a: f32, b: f32) -> [f32; 2] { [a, b] }
// </vc-helpers>

// <vc-spec>
fn chebline(off: f32, scl: f32) -> (result: [f32; 2])
    ensures 
        result[0] == off,
        result[1] == scl
// </vc-spec>
// <vc-code>
{
    [off, scl]
}
// </vc-code>

}
fn main() {}