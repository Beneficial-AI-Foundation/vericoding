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
/* helper modified by LLM (iteration 4): [brief description] */

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
/* code modified by LLM (iteration 4): [brief description] */
{
    // Use a wider type (u32) for the multiplication to prevent overflow.
    // The product of two u8s (max 255*255 = 65025) fits within a u16, but u32 is safer
    // and helps resolve verifier confusion about potential overflows.
    let area = (base as u32 * height as u32) / 2;

    // This proof block connects the implementation's logic with the specification's formula.
    // It asserts that the mathematical value of `area` (calculated with u32)
    // is identical to the value from `triangle_area_formula` (calculated with int).
    proof {
        assert(area as int == triangle_area_formula(base as int, height as int));
    }

    // The a final cast to u8 is required. This cast can be lossy if `area > 255`.
    // The ensures clause `(area as u8) as int == triangle_area_formula(...)` requires this cast
    // to be lossless. Since the `requires` clause does not guarantee `area <= 255`,
    // Verus cannot prove the postcondition for all inputs. The spec is unimplementable.
    // However, this implementation is the most direct translation of the math.
    area as u8
}

// </vc-code>


}

fn main() {}