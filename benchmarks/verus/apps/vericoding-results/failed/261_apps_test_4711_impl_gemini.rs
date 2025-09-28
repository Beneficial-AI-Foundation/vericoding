// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 10000 && 1 <= b <= 10000 && 1 <= c <= 10000
}

spec fn min_of_three(x: int, y: int, z: int) -> int {
    if x <= y && x <= z { x }
    else if y <= z { y }
    else { z }
}

spec fn correct_result(a: int, b: int, c: int) -> int {
    min_of_three(a + b, a + c, b + c)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): mirrors spec function logic for clarity */
fn min3(x: i16, y: i16, z: i16) -> (res: i16)
    ensures
        res as int == min_of_three(x as int, y as int, z as int),
{
    if x <= y && x <= z {
        x
    } else if y <= z {
        y
    } else {
        z
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires valid_input(a as int, b as int, c as int)
    ensures result as int == correct_result(a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): simplified body to essential logic */
{
    // Widen types to i16 to avoid overflow, matching the `int` arithmetic in the spec.
    let sum_ab = (a as i16) + (b as i16);
    let sum_ac = (a as i16) + (c as i16);
    let sum_bc = (b as i16) + (c as i16);

    // Calculate the minimum of the three sums using the helper.
    let min_val: i16 = min3(sum_ab, sum_ac, sum_bc);

    // The spec is unsatisfiable because for some valid inputs, `min_val` exceeds
    // the `i8` range. This cast will correctly fail verification.
    min_val as i8
}
// </vc-code>


}

fn main() {}