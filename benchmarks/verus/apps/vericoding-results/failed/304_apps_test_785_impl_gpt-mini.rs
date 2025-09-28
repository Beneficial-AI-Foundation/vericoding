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
/* helper modified by LLM (iteration 5): safe ceil division that handles nonpositive divisor */
spec fn ceil_div(x: int, y: int) -> int {
    if y <= 0 { 0 } else { (x + y - 1) / y }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8) -> (result: Vec<i8>)
    requires valid_input(n as int, a as int, b as int)
    ensures valid_output(result@.map(|i, x| x as int), n as int, a as int, b as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use i64 arithmetic and double the smaller dimension until product >= need */
{
    let need: i64 = 6 * (n as i64);
    let mut A: i64 = a as i64;
    let mut B: i64 = b as i64;
    while A * B < need
        invariant
            A > 0,
            B > 0,
            A >= a as i64,
            B >= b as i64,
        decreases
            need - A * B
    {
        if A <= B {
            A = A * 2;
        } else {
            B = B * 2;
        }
    }
    let mut res: Vec<i8> = Vec::new();
    res.push((A * B) as i8);
    res.push(A as i8);
    res.push(B as i8);
    res
}
// </vc-code>


}

fn main() {}