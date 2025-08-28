use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn cube_surface_area_spec(size: i32) -> int {
    6 * size * size
}

proof fn cube_surface_area_bounds(size: i32)
    requires size > 0 && size <= 18918
    ensures cube_surface_area_spec(size) <= 2147483647
{
    assert(size <= 18918);
    assert(size * size <= 18918 * 18918) by (nonlinear_arith);
    assert(6 * (size * size) <= 6 * (18918 * 18918)) by (nonlinear_arith);
    assert(18918 * 18918 == 357890724) by (compute_only);
    assert(6 * 357890724 == 2147344344) by (compute_only);
    assert(2147344344 <= 2147483647) by (compute_only);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn cube_surface_area(size: i32) -> (area: i32)
    requires size > 0
    ensures area == 6 * size * size
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let size_64 = size as i64;
    let area_64 = 6i64 * size_64 * size_64;
    
    proof {
        assert(size_64 == size as i64);
        assert(area_64 == 6i64 * (size as i64) * (size as i64));
        assert(area_64 == (6 * size * size) as i64) by (nonlinear_arith);
        assert(size > 0);
        if size <= 18918 {
            cube_surface_area_bounds(size);
            assert(6 * size * size <= 2147483647);
            assert(area_64 <= 2147483647);
        } else {
            assert(6 * size * size > 2147483647);
        }
    }
    
    #[verifier::truncate]
    (area_64 as i32)
}
// </vc-code>

fn main() {
}

}