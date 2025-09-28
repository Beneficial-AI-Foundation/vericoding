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
/* helper modified by LLM (iteration 5): Add i8 version of min_of_three and helper to find min of two i8 values */
spec fn min_of_three_i8(x: i8, y: i8, z: i8) -> i8 {
    if x <= y && x <= z { x }
    else if y <= z { y }
    else { z }
}

spec fn min_of_two(a: i8, b: i8) -> i8 {
    if a <= b { a } else { b }
}

/* helper modified by LLM (iteration 5): Add safe_add helper to prevent overflow */
fn safe_add(a: i8, b: i8) -> (sum: i8)
    requires
        a as int >= 0,
        b as int >= 0,
        a as int + b as int <= core::i8::MAX as int,
    ensures
        sum as int == a as int + b as int
{
    a + b
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires valid_input(a as int, b as int, c as int)
    ensures result as int == correct_result(a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use safe_add and manually compute min of three using nested min_of_two calls */
{
    let ab = safe_add(a, b);
    let ac = safe_add(a, c);
    let bc = safe_add(b, c);
    let result = min_of_two(min_of_two(ab, ac), bc);
    result
}
// </vc-code>


}

fn main() {}