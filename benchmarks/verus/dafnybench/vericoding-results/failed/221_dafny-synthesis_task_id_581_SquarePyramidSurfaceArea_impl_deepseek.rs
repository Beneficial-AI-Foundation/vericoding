use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn square_pyramid_surface_area_formula(base_edge: nat, height: nat)
    ensures
        base_edge * base_edge + 2 * base_edge * height == base_edge * base_edge + 2 * base_edge * height,
{
}

proof fn arithmetic_safe(base_edge: nat, height: nat)
    requires
        base_edge as int <= i32::MAX as int,
        height as int <= i32::MAX as int,
        (base_edge as int) * (base_edge as int) <= i32::MAX as int,
        2 * (base_edge as int) * (height as int) <= i32::MAX as int,
    ensures
        (base_edge as int) * (base_edge as int) <= i32::MAX,
        2 * (base_edge as int) * (height as int) <= i32::MAX,
        (base_edge as int) * (base_edge as int) + 2 * (base_edge as int) * (height as int) <= i32::MAX,
{
}
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
    proof {
        assert(base_edge > 0);
        assert(height > 0);
        assert(base_edge as int <= i32::MAX as int);
        assert(height as int <= i32::MAX as int);
        assert((base_edge as int) * (base_edge as int) <= i32::MAX as int);
        assert(2 * (base_edge as int) * (height as int) <= i32::MAX as int);
        arithmetic_safe(base_edge as nat, height as nat);
    }
    let be_sq: i32 = base_edge * base_edge;
    let term2: i32 = (2u32 as i32).checked_mul(base_edge).unwrap().checked_mul(height).unwrap();
    let area: i32 = be_sq.checked_add(term2).unwrap();
    proof { square_pyramid_surface_area_formula(base_edge as nat, height as nat); }
    area
}
// </vc-code>

fn main() {
}

}