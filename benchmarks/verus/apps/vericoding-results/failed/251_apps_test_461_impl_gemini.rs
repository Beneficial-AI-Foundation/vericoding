// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int, c: int) -> bool {
    1 <= n <= 100 && 1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

spec fn min_distance(n: int, a: int, b: int, c: int) -> int
    recommends valid_input(n, a, b, c)
{
    if n == 1 { 0 } else { (n - 1) * min(a, b) }
}

spec fn min(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

spec fn max(x: int, y: int) -> int {
    if x >= y { x } else { y }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Retained correct helper function. */
fn min_i8(a: i8, b: i8) -> (res: i8)
    ensures
        res as int == min(a as int, b as int),
{
    if a <= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, c: i8) -> (result: i8)
    requires 
        valid_input(n as int, a as int, b as int, c as int)
    ensures 
        result >= 0,
        n == 1 ==> result == 0,
        result as int <= (n as int - 1) * max(a as int, max(b as int, c as int)),
        result as int == min_distance(n as int, a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed compilation error by using i16 for calculation. */
    if n == 1 {
        0
    } else {
        let min_val = min_i8(a, b);
        let result_i16 = (n as i16 - 1) * (min_val as i16);
        result_i16 as i8
    }
}
// </vc-code>


}

fn main() {}