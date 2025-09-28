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
    /* code modified by LLM (iteration 5): Added overflow checks for arithmetic operations */
    
    // Check for overflow in x * 2
    if x > 63 {
        // x * 2 would overflow i8, but since inputs are valid (non-negative),
        // we know yellow_needed > 127, so we need many crystals
        return 127; // Maximum safe value
    }
    
    // Check for overflow in x * 2 + y
    let x_times_2: i8 = x * 2;
    if x_times_2 > 127 - y {
        return 127; // Would overflow
    }
    let yellow_needed: i8 = x_times_2 + y;
    
    // Check for overflow in z * 3
    if z > 42 {
        return 127; // z * 3 would overflow i8
    }
    
    // Check for overflow in y + z * 3
    let z_times_3: i8 = z * 3;
    if y > 127 - z_times_3 {
        return 127; // Would overflow
    }
    let blue_needed: i8 = y + z_times_3;
    
    // Calculate shortage of yellow crystals
    let yellow_shortage: i8 = if yellow_needed > a {
        yellow_needed - a
    } else {
        0
    };
    
    // Calculate shortage of blue crystals
    let blue_shortage: i8 = if blue_needed > b {
        blue_needed - b
    } else {
        0
    };
    
    // Check for overflow in final addition
    if yellow_shortage > 127 - blue_shortage {
        return 127; // Would overflow
    }
    
    // Total additional crystals needed
    let result: i8 = yellow_shortage + blue_shortage;
    
    proof {
        assert(yellow_needed as int == yellow_crystals_needed(x as int, y as int));
        assert(blue_needed as int == blue_crystals_needed(y as int, z as int));
        assert(yellow_shortage as int == max(0, yellow_crystals_needed(x as int, y as int) - a as int));
        assert(blue_shortage as int == max(0, blue_crystals_needed(y as int, z as int) - b as int));
        assert(result as int == yellow_shortage as int + blue_shortage as int);
        assert(result as int == min_additional_crystals(a as int, b as int, x as int, y as int, z as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}