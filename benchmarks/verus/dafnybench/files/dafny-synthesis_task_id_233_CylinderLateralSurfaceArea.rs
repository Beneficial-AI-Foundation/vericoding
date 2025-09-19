// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn cylinder_lateral_surface_area(radius: u8, height: u8) -> (area: u8)
    requires 
        radius > 0,
        height > 0,
    ensures area as nat == 2 * radius as nat * height as nat * 314 / 100,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}