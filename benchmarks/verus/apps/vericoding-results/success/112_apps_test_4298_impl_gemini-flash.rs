// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, d: int) -> bool {
    n >= 1 && n <= 20 && d >= 1 && d <= 20
}

spec fn coverage_range(position: int, d: int) -> (int, int) {
    (position - d, position + d)
}

spec fn trees_covered(n: int, d: int, inspectors: int) -> bool {
    inspectors >= 1 && inspectors <= n && inspectors == ((n - 1) / (2 * d + 1)) + 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): provide an empty helper section to satisfy the JSON structure requirements */
// </vc-helpers>

// <vc-spec>
fn min_inspectors(n: i8, d: i8) -> (result: i8)
    requires valid_input(n as int, d as int)
    ensures trees_covered(n as int, d as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fix `int` conversion errors by using `as` to convert Verus `int` to `i8` for the body, while keeping the spec uses of `int` as is. */
{
    let n_calc: i8 = n;
    let d_calc: i8 = d;
    let two_d_plus_one: i8 = 2 * d_calc + 1;
    let quotient: i8 = (n_calc - 1) / two_d_plus_one;
    let result: i8 = quotient + 1;
    result
}
// </vc-code>


}

fn main() {}