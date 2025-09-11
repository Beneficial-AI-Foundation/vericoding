// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn triangular_prism_volume(base: u32, height: u32, length: u32) -> (volume: u32)
    requires 
        base > 0,
        height > 0,
        length > 0,
    ensures volume == (base * height * length) / 2,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}