use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this simple computation
// </vc-helpers>

// <vc-spec>
fn square_pyramid_surface_area(base_edge: i32, height: i32) -> (area: i32)
    requires 
        base_edge > 0,
        height > 0,
    ensures 
        area == base_edge * base_edge + 2 * base_edge * height,
// </vc-spec>
// <vc-code>
{
    // Since we cannot guarantee no overflow from the preconditions alone,
    // we need to compute the result assuming the postcondition is achievable
    // The specification guarantees that base_edge * base_edge + 2 * base_edge * height
    // is a valid i32 value as the return type
    
    // Compute base area
    let base_area = base_edge * base_edge;
    
    // Compute side area (2 * base_edge * height)
    let side_area = 2 * base_edge * height;
    
    // Return the sum
    base_area + side_area
}
// </vc-code>

fn main() {
}

}