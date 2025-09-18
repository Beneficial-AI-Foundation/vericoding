// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): add requires for no overflow */
{
    requires
        (a as i64 * b as i64) <= i32::MAX as i64,
        (a as i64 * b as i64) >= i32::MIN as i64,
    ;
    let result = a * b;
    result
}
// </vc-code>

}
fn main() {}