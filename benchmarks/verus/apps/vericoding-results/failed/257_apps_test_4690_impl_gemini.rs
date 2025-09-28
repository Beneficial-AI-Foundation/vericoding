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
/* helper modified by LLM (iteration 4): add precondition to prove no overflow */
fn safe_mul(x: i8, y: i8) -> (res: i32)
    requires
        x > 0,
        y > 0,
        (x as int) * (y as int) <= i32::MAX,
    ensures
        res as int == (x as int) * (y as int),
{
    (x as i32) * (y as i32)
}
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
{
    /* code modified by LLM (iteration 4): use i32 helper, but spec contradiction remains */
    let area1 = safe_mul(a, b);
    let area2 = safe_mul(c, d);

    if area1 >= area2 {
        area1 as i8
    } else {
        area2 as i8
    }
}
// </vc-code>


}

fn main() {}