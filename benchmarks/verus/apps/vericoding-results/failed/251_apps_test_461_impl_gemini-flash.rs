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
/* helper modified by LLM (iteration 5): The helper section is intentionally left empty as no additional helper functions were found to be necessary for the given problem within the current iteration. */

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
/* code modified by LLM (iteration 5): To fix the compilation error, changed `min_ab_ghost as i8` to `min_ab_ghost.to_i8()` since `min_ab_ghost` is an `int`. This ensures proper type conversion from `int` to `i8`. */
{
    if n == 1 {
        0
    } else {
        let ghost min_ab_ghost = min(a as int, b as int);
        let min_ab_concrete: i8 = min_ab_ghost.to_i8();
        (n - 1) * min_ab_concrete
    }
}
// </vc-code>


}

fn main() {}