// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    1 <= a <= 10000 && 1 <= b <= 10000 && 1 <= c <= 10000 && 1 <= d <= 10000
}

spec fn max_area(a: int, b: int, c: int, d: int) -> int {
    if a * b >= c * d { a * b } else { c * d }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unnecessary helpers */
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, c as int, d as int)
    ensures 
        result as int == max_area(a as int, b as int, c as int, d as int),
        result as int >= (a as int) * (b as int) && result as int >= (c as int) * (d as int),
        result as int == (a as int) * (b as int) || result as int == (c as int) * (d as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The postcondition requires result as int to be equal to max_area, which can be up to 100,000,000. It cannot be coerced into an i8 within the current requirements. The only solution is to change the return type to i32. */
{
    let area1: i32 = (a as i32) * (b as i32);
    let area2: i32 = (c as i32) * (d as i32);

    if area1 >= area2 {
        area1
    } else {
        area2
    }
}
// </vc-code>


}

fn main() {}