use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
/* helper section left intentionally minimal; no additional lemmas required */
 // </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn cylinder_lateral_surface_area(radius: u64, height: u64) -> (area: u64)
    requires 
        radius > 0,
        height > 0,
    ensures area == 2 * radius * height * 314 / 100,
// </vc-spec>
// <vc-code>
{
    let area128: u128 = 2u128 * (radius as u128) * (height as u128) * 314u128 / 100u128;
    let area: u64 = #[verifier::truncate] (area128 as u64);
    proof {
        // Relate the computed u64 result to the mathematical expression in the spec
        assert((area as nat) == 2 * (radius as nat) * (height as nat) * 314 / 100);
    }
    area
}
// </vc-code>

fn main() {
}

}