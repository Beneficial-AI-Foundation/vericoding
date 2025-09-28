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
/* helper modified by LLM (iteration 5): added overflow check for u8 multiplication */
fn checked_multiply_u8(a: u8, b: u8) -> (result: u8)
    requires
        a as int * b as int <= 255
    ensures
        result as int == a as int * b as int
{
    a * b
}

/* helper modified by LLM (iteration 5): added lemma for triangle area properties */
proof fn triangle_area_properties(base: int, height: int)
    requires
        base >= 0,
        height >= 0
    ensures
        (base == 0 || height == 0) ==> triangle_area_formula(base, height) == 0,
        triangle_area_formula(base, height) >= 0
{
    if base == 0 || height == 0 {
        assert(triangle_area_formula(base, height) == 0);
    }
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
    /* code modified by LLM (iteration 5): fixed ghost type usage by moving to proof blocks */
    if base == 0 || height == 0 {
        return 0;
    }
    
    // Check for overflow before multiplication
    proof {
        let base_int = base as int;
        let height_int = height as int;
        
        if base_int * height_int > 255 {
            return 0;
        }
    }
    
    let product = checked_multiply_u8(base, height);
    let area = product / 2;
    
    proof {
        triangle_area_properties(base as int, height as int);
        assert(area as int == triangle_area_formula(base as int, height as int));
    }
    
    area
}
// </vc-code>


}

fn main() {}