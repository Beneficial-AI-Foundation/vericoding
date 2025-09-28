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
/* code modified by LLM (iteration 5): removed ghost keyword from let statements in proof block */
{
    // Convert inputs to i32 to avoid overflow and use in executable code
    let a_i32 = a as i32;
    let b_i32 = b as i32;
    let x_i32 = x as i32;
    let y_i32 = y as i32;
    let z_i32 = z as i32;

    // Compute yellow crystals needed: x*2 + y
    let yellow_needed = x_i32 * 2 + y_i32;

    // Compute blue crystals needed: y + z*3
    let blue_needed = y_i32 + z_i32 * 3;

    // Compute additional yellow crystals needed
    let additional_yellow = if yellow_needed > a_i32 {
        yellow_needed - a_i32
    } else {
        0
    };

    // Compute additional blue crystals needed
    let additional_blue = if blue_needed > b_i32 {
        blue_needed - b_i32
    } else {
        0
    };

    // Total additional crystals
    let total = additional_yellow + additional_blue;

    // Cast to i8 and return
    let result = total as i8;

    // Proof block to verify the result
    proof {
        // Convert inputs to int for spec functions
        let a_int = a as int;
        let b_int = b as int;
        let x_int = x as int;
        let y_int = y as int;
        let z_int = z as int;

        // Compute the spec values
        let yellow_needed_spec = yellow_crystals_needed(x_int, y_int);
        let blue_needed_spec = blue_crystals_needed(y_int, z_int);
        let additional_yellow_spec = if yellow_needed_spec > a_int {
            yellow_needed_spec - a_int
        } else {
            0
        };
        let additional_blue_spec = if blue_needed_spec > b_int {
            blue_needed_spec - b_int
        } else {
            0
        };
        let total_spec = additional_yellow_spec + additional_blue_spec;

        // The i32 computation matches the int computation because the values are the same and operations are the same
        assert(total as int == total_spec);
        assert(total_spec == min_additional_crystals(a_int, b_int, x_int, y_int, z_int));
        assert(total >= 0);   // because both additional terms are non-negative
    }

    result
}
// </vc-code>


}

fn main() {}