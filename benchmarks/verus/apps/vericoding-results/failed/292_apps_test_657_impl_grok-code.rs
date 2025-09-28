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
    let yellow_needed: i32 = x as i32 * 2 + y as i32;
    let blue_needed: i32 = y as i32 + z as i32 * 3;
    let add_yellow: i32 = if yellow_needed > a as i32 { yellow_needed - a as i32 } else { 0 };
    let add_blue: i32 = if blue_needed > b as i32 { blue_needed - b as i32 } else { 0 };
    (add_yellow + add_blue) as i8
}
// </vc-code>


}

fn main() {}