// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed unnecessary function, problem statement does not provide context for it. */
// </vc-helpers>

// <vc-spec>
fn max_of_three(a: i32, b: i32, c: i32) -> (result: i32)
    ensures
        result >= a && result >= b && result >= c,
        result == a || result == b || result == c,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed recursive call and set max_of_three to return the maximum of the three numbers using if-else statements. */ {
    if a >= b && a >= c {
        a
    } else if b >= a && b >= c {
        b
    } else {
        c
    }
}
// </vc-code>

}
fn main() {}