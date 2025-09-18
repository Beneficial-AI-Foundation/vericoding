// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): removed non-spec to_int function */
spec fn min(a: int, b: int) -> int {
    if a < b {
        a
    } else {
        b
    }
}
// </vc-helpers>

// <vc-spec>
fn min_of_three(a: i32, b: i32, c: i32) -> (result: i32)
    ensures
        result <= a && result <= b && result <= c,
        result == a || result == b || result == c,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): removed to_int calls, used direct i32 comparisons */
{
    let min_ab = if a < b { a } else { b };
    if min_ab < c { min_ab } else { c }
}
// </vc-code>

}
fn main() {}