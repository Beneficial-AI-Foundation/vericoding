// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed type conversion in safe multiplication */
fn safe_multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
{
    (a as i64 * b as i64) as i32
}
// </vc-helpers>

// <vc-spec>
fn multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): using corrected safe multiplication helper */
{
    let result = safe_multiply(a, b);
    result
}
// </vc-code>

}
fn main() {}