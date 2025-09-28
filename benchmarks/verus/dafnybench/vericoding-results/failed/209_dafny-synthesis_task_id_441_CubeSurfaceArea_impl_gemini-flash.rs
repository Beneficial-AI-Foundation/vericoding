use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(inline)]
spec fn mul_is_pos(a: int, b: int) -> bool {
    a > 0 && b > 0 ==> a * b > 0
}
// </vc-helpers>

// <vc-spec>
fn cube_surface_area(size: i32) -> (area: i32)
    requires size > 0
    ensures area == 6 * size * size
// </vc-spec>
// <vc-code>
{
    // Proof that 6 * size will not overflow/underflow if size is positive
    // and that the result will also be positive.
    proof {
        assert(mul_is_pos(6, size as int));
        assert(mul_is_pos(6 * size as int, size as int));
    }

    let area: i32 = 6 * size * size;
    area
}
// </vc-code>

fn main() {
}

}