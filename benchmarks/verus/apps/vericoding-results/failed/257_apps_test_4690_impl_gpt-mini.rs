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
spec fn max_i(x: int, y: int) -> int
    ensures
        result == if x >= y { x } else { y },
{
    if x >= y { x } else { y }
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
    let area1: int = (a as int) * (b as int);
    let area2: int = (c as int) * (d as int);
    let m: int = max_i(area1, area2);
    if m == area1 {
        m as i8
    } else {
        m as i8
    }
}
// </vc-code>


}

fn main() {}