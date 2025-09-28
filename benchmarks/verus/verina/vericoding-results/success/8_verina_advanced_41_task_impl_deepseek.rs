// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn max_of_two(a: i32, b: i32) -> (result: i32)
    ensures
        result >= a && result >= b,
        result == a || result == b,
{
    if a >= b {
        a
    } else {
        b
    }
}
// </vc-helpers>

// <vc-spec>
fn max_of_three(a: i32, b: i32, c: i32) -> (result: i32)
    ensures
        result >= a && result >= b && result >= c,
        result == a || result == b || result == c,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Use executable max function */
    let ab_max = if a >= b { a } else { b };
    let result = if ab_max >= c { ab_max } else { c };
    result
}
// </vc-code>

}
fn main() {}