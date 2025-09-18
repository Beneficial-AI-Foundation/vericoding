// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added ensures clauses to verify the min function correctly returns the minimum and satisfies equality */
exec fn min(a: i32, b: i32) -> (result: i32)
    ensures
        result <= a && result <= b,
        result == a || result == b,
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
    /* code modified by LLM (iteration 3): Implemented correct min finding logic using the helper */
    let m_ab = min(a, b);
    let result = min(m_ab, c);
    result
}
// </vc-code>

}
fn main() {}