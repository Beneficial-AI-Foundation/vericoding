// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(base: int, height: int) -> bool {
    base >= 0 && height >= 0
}

spec fn triangle_area_formula(base: int, height: int) -> int {
    (base * height) / 2
}

spec fn triangle_area(a: int, h: int) -> int {
    (a * h) / 2
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): strengthen product bound proof without relying on monotonic step */
proof fn area_zero_when_zero(base: u8, height: u8)
    ensures
        (base == 0 || height == 0) ==> triangle_area_formula(base as int, height as int) == 0,
{
    let a: int = base as int;
    let b: int = height as int;
    if base == 0 || height == 0 {
        assert(triangle_area_formula(a, b) == (a * b) / 2);
        if base == 0 {
            assert(a == 0);
            assert(a * b == 0);
        } else {
            assert(height == 0);
            assert(b == 0);
            assert(a * b == 0);
        }
        assert((a * b) / 2 == 0);
        assert(triangle_area_formula(a, b) == 0);
    }
}

/* helper modified by LLM (iteration 5): nonnegativity of triangle area */
proof fn triangle_area_nonnegative(base: u8, height: u8)
    ensures
        triangle_area_formula(base as int, height as int) >= 0,
{
    let a: int = base as int;
    let b: int = height as int;
    assert(a >= 0);
    assert(b >= 0);
    assert(a * b >= 0);
    assert(triangle_area_formula(a, b) == (a * b) / 2);
    assert((a * b) / 2 >= 0);
}

/* helper modified by LLM (iteration 5): bound product of two u8 values without monotonic step */
proof fn u8_product_bound(base: u8, height: u8)
    ensures
        0 <= (base as int) * (height as int),
        (base as int) * (height as int) <= 65535,
{
    let a: int = base as int;
    let b: int = height as int;
    assert(a >= 0);
    assert(b >= 0);
    assert(a * b >= 0);
    assert(a <= 255);
    assert(b <= 255);
    assert(a * b <= 255 * 255) by (nonlinear_arith);
    assert(255 * 255 == 65025);
    assert(a * b <= 65025);
    assert(65025 <= 65535);
}

/* helper modified by LLM (iteration 5): relate u16 computation to int specification when no wraparound occurs */
proof fn u16_mul_div_matches_int(base: u8, height: u8)
    ensures
        (((base as u16) * (height as u16)) / 2u16) as int == triangle_area_formula(base as int, height as int),
{
    let a: int = base as int;
    let b: int = height as int;
    // product fits within 16 bits
    u8_product_bound(base, height);
    assert(a * b <= 65535);
    // Casting u8 to u16 then to int preserves values
    assert(((base as u16) as int) == a);
    assert(((height as u16) as int) == b);
    // With no wraparound, u16 multiplication equals int multiplication
    assert((((base as u16) * (height as u16)) as int) == a * b);
    // Division by 2 is consistent between u16 and int when interpreted as mathematical ints
    assert((((base as u16) * (height as u16)) / 2u16) as int == (((base as u16) * (height as u16)) as int) / 2);
    assert(triangle_area_formula(a, b) == (a * b) / 2);
}

// </vc-helpers>

// <vc-spec>
fn calculate_triangle_area(base: u8, height: u8) -> (area: u8)
    requires 
        valid_input(base as int, height as int)
    ensures 
        area as int >= 0,
        area as int == triangle_area_formula(base as int, height as int),
        (base == 0 || height == 0) ==> area == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute area via u16 path; prove zero case and link to spec */
    proof {
        area_zero_when_zero(base, height);
        triangle_area_nonnegative(base, height);
        u8_product_bound(base, height);
    }

    if base == 0 || height == 0 {
        let area: u8 = 0u8;
        area
    } else {
        // Compute using wider type to avoid intermediate overflow
        let prod_u16: u16 = (base as u16) * (height as u16);
        let area_u16: u16 = prod_u16 / 2u16;
        let area: u8 = area_u16 as u8;

        proof {
            // Connect executable computation to spec formula (as mathematical ints)
            u16_mul_div_matches_int(base, height);
            let a: int = base as int;
            let b: int = height as int;
            assert((area_u16 as int) == triangle_area_formula(a, b));
            // When area_u16 fits into u8, casting preserves the integer value
            if area_u16 <= 255u16 {
                assert(area as int == area_u16 as int);
            }
        }
        area
    }
}
// </vc-code>


}

fn main() {}