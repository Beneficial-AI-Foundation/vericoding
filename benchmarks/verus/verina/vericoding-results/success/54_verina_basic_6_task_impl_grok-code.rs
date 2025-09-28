// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: i32, b: i32) -> (r: i32)
    ensures
        r <= a && r <= b && (r == a || r == b)
{
    if a < b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn min_of_three(a: i32, b: i32, c: i32) -> (result: i32)
    ensures
        result <= a && result <= b && result <= c,
        result == a || result == b || result == c,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implementing min_of_three using helper */
    let ab = min(a, b);
    min(ab, c)
}
// </vc-code>

}
fn main() {}