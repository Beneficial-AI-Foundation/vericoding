// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn id_int(a: int) -> int {
    a
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
    let res: [f32; 2] = [off, scl];
    res
}
// </vc-code>

}
fn main() {}