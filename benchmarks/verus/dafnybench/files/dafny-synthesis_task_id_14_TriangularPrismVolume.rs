// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn triangular_prism_volume(base: u8, height: u8, length: u8) -> (volume: u8)
    requires 
        base > 0,
        height > 0,
        length > 0,
    ensures volume as nat == (base as nat * height as nat * length as nat) / 2,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}