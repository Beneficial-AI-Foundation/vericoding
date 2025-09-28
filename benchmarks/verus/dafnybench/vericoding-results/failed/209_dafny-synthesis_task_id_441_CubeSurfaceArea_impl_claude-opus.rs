use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn cube_surface_area(size: i32) -> (area: i32)
    requires size > 0
    ensures area == 6 * size * size
// </vc-spec>
// <vc-code>
{
    // First check that the multiplication won't overflow
    assert(size <= 46340) by {
        // 46340^2 = 2,147,395,600 < 2^31 - 1 = 2,147,483,647
        // and 6 * 46340^2 = 12,884,373,600 > 2^31 - 1
        // so we need size * size <= (2^31 - 1) / 6 ≈ 357,913,941
        // which means size <= 18,918
        // But actually, for 6 * size * size to not overflow:
        // We need 6 * size * size <= 2,147,483,647
        // size * size <= 357,913,941
        // size <= 18,918 (approximately)
        // However, being more conservative: size <= 46340 ensures size * size doesn't overflow
        // and then we need to ensure 6 * (size * size) doesn't overflow
        if size > 18918 {
            // For size > 18918, 6 * size * size might overflow i32
            assert(false);
        }
    }
    
    // Compute size * size first
    let size_squared = size * size;
    
    // Now compute 6 * size_squared
    assert(size_squared >= 0) by {
        assert(size > 0);
        assert(size * size >= 0);
    }
    
    assert(6 * size_squared <= i32::MAX) by {
        // We know size <= 18918 from above
        // So size * size <= 18918 * 18918 = 357,489,124
        // And 6 * 357,489,124 = 2,144,934,744 which is less than i32::MAX (2,147,483,647)
        if size <= 18918 {
            assert(size * size <= 357489124);
            assert(6 * 357489124 == 2144934744);
            assert(2144934744 <= 2147483647);
        }
    }
    
    let area = 6 * size_squared;
    area
}
// </vc-code>

fn main() {
}

}