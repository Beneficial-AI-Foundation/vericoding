// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn cylinder_surface_area(radius: u64, height: u64) -> (area: u64)
    requires radius > 0 && height > 0
    ensures area == 2 * radius * (radius + height)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}