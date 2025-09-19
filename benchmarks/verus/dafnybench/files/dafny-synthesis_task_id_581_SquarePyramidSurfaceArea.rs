// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn square_pyramid_surface_area(base_edge: i8, height: i8) -> (area: i8)
    requires 
        base_edge > 0,
        height > 0,
    ensures 
        area as int == base_edge as int * base_edge as int + 2 * base_edge as int * height as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}