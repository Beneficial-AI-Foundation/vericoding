// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int) -> bool {
    n > 0 && a > 0 && b > 0
}

spec fn valid_output(result: Seq<int>, n: int, a: int, b: int) -> bool {
    result.len() == 3 &&
    result[0] >= 6 * n &&
    result[1] > 0 && result[2] > 0 &&
    result[0] == result[1] * result[2] &&
    ((result[1] >= a && result[2] >= b) || (result[1] >= b && result[2] >= a))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added spec functions for max and min on int */
spec fn max_int(a: int, b: int) -> int {
    if a > b { a } else { b }
}

spec fn min_int(a: int, b: int) -> int {
    if a < b { a } else { b }
}

fn max(a: i8, b: i8) -> i8 {
    if a > b { a } else { b }
}

fn min(a: i8, b: i8) -> i8 {
    if a < b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8) -> (result: Vec<i8>)
    requires valid_input(n as int, a as int, b as int)
    ensures valid_output(result@.map(|i, x| x as int), n as int, a as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariant to use spec function max_int */
    let mut y = max(a, b) as i32;
    let min_val = min(a, b) as i32;
    while y <= 127
        invariant
            y >= max_int(a as int, b as int) && y <= 128,
        decreases 128 - y
    {
        let z0 = (6 * (n as i32) + y - 1) / y;   // ceil(6*n/y)
        let z = if z0 < min_val { min_val } else { z0 };
        if y * z <= 127 {
            return vec![(y * z) as i8, y as i8, z as i8];
        }
        y = y + 1;
    }
    // Fallback: no solution found, return zeros (will not satisfy postcondition but avoids overflow)
    vec![0, 0, 0]
}
// </vc-code>


}

fn main() {}