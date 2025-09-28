// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

spec fn valid_input(a: int, b: int, x: int, y: int, z: int) -> bool {
    a >= 0 && b >= 0 && x >= 0 && y >= 0 && z >= 0
}

spec fn yellow_crystals_needed(x: int, y: int) -> int {
    x * 2 + y
}

spec fn blue_crystals_needed(y: int, z: int) -> int {
    y + z * 3
}

spec fn min_additional_crystals(a: int, b: int, x: int, y: int, z: int) -> int {
    max(0, yellow_crystals_needed(x, y) - a) + max(0, blue_crystals_needed(y, z) - b)
}
// </vc-preamble>

// <vc-helpers>
// Helper function to compute max of two i8 values
fn max_i8(a: i8, b: i8) -> (result: i8)
    requires
        a >= 0,
        b >= 0
    ensures
        result >= 0,
        result as int == max(a as int, b as int)
{
    if a >= b { a } else { b }
}

// Helper function to safely subtract with floor at 0
fn safe_subtract(a: i8, b: i8) -> (result: i8)
    requires
        a >= 0,
        b >= 0
    ensures
        result >= 0,
        result as int == max(0, a as int - b as int)
{
    if a >= b { a - b } else { 0 }
}

/* helper modified by LLM (iteration 5): Fixed preconditions for safe arithmetic */
fn safe_add_i8(a: i8, b: i8) -> (result: i8)
    requires
        a >= 0,
        b >= 0,
        a as int + b as int < 128
    ensures
        result >= 0,
        result as int == a as int + b as int
{
    a + b
}

/* helper modified by LLM (iteration 5): Fixed preconditions for safe multiplication */
fn safe_multiply_i8(a: i8, b: i8) -> (result: i8)
    requires
        a >= 0,
        b >= 0,
        a as int * b as int < 128
    ensures
        result >= 0,
        result as int == a as int * b as int
{
    a * b
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, x: i8, y: i8, z: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, x as int, y as int, z as int)
    ensures 
        result >= 0,
        result as int == min_additional_crystals(a as int, b as int, x as int, y as int, z as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Using safe arithmetic helpers to avoid overflow */
    let yellow_x_part = safe_multiply_i8(x, 2);
    let yellow_needed = safe_add_i8(yellow_x_part, y);
    let blue_z_part = safe_multiply_i8(z, 3);
    let blue_needed = safe_add_i8(y, blue_z_part);
    
    let yellow_deficit = safe_subtract(yellow_needed, a);
    let blue_deficit = safe_subtract(blue_needed, b);
    
    safe_add_i8(yellow_deficit, blue_deficit)
}
// </vc-code>


}

fn main() {}