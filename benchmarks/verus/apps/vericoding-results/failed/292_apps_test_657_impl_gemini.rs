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
{
    let a_as_i32 = a as i32;
    let b_as_i32 = b as i32;
    let x_as_i32 = x as i32;
    let y_as_i32 = y as i32;
    let z_as_i32 = z as i32;

    let yellow_needed = x_as_i32 * 2 + y_as_i32;
    let blue_needed = y_as_i32 + z_as_i32 * 3;

    let yellow_to_buy = if yellow_needed > a_as_i32 {
        yellow_needed - a_as_i32
    } else {
        0
    };

    let blue_to_buy = if blue_needed > b_as_i32 {
        blue_needed - b_as_i32
    } else {
        0
    };

    let total_needed = yellow_to_buy + blue_to_buy;
    
    total_needed as i8
}
// </vc-code>


}

fn main() {}