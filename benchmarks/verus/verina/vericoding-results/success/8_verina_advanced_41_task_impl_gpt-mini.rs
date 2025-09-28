// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): executable helper to compute max of two integers */
fn max2(a: i32, b: i32) -> (result: i32)
    ensures
        result >= a && result >= b,
        result == a || result == b,
{
    if a >= b { a } else { b }
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
    /* code modified by LLM (iteration 4): compute max of three using helper max2 */
    let m = max2(a, b);
    let result = max2(m, c);
    result
}
// </vc-code>

}
fn main() {}