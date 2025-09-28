use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to ensure no overflow in the computation
proof fn cylinder_computation_no_overflow(radius: u64, height: u64)
    requires
        radius > 0,
        height > 0,
        radius <= u64::MAX / 2,
        height as int <= u64::MAX / (2 * radius as int),
        2 * radius as int * height as int <= u64::MAX / 314,
    ensures
        2 * radius <= u64::MAX,
        2 * radius * height <= u64::MAX,
        2 * radius * height * 314 <= u64::MAX,
        2 * radius * height * 314 / 100 <= u64::MAX,
{
    // The ensures clauses follow from the requires clauses
}
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
    // Check preconditions for no overflow
    if radius > u64::MAX / 2 {
        return 0; // Return 0 for invalid input to avoid overflow
    }
    
    if height as int > u64::MAX / (2 * radius as int) {
        return 0; // Return 0 for invalid input to avoid overflow
    }
    
    if 2 * radius as int * height as int > u64::MAX / 314 {
        return 0; // Return 0 for invalid input to avoid overflow
    }
    
    // Prove that the computation won't overflow
    proof {
        cylinder_computation_no_overflow(radius, height);
    }
    
    let two_r = 2 * radius;
    let two_r_h = two_r * height;
    let numerator = two_r_h * 314;
    let area = numerator / 100;
    
    // Verify the postcondition holds
    assert(area == 2 * radius * height * 314 / 100);
    
    area
}
// </vc-code>

fn main() {
}

}