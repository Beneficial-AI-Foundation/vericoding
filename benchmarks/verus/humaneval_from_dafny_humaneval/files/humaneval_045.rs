// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(base: int, height: int) -> bool {
    base >= 0 && height >= 0
}

spec fn triangle_area_formula(base: int, height: int) -> int {
    (base * height) / 2
}
// </vc-preamble>

// <vc-helpers>
spec fn triangle_area(a: int, h: int) -> int {
    (a * h) / 2
}
// </vc-helpers>

// <vc-spec>
fn calculate_triangle_area(base: int, height: int) -> (area: int)
    requires 
        valid_input(base, height)
    ensures 
        area >= 0,
        area == triangle_area_formula(base, height),
        (base == 0 || height == 0) ==> area == 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}