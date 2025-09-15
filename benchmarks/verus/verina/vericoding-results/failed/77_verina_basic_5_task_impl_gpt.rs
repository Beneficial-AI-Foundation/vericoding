// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec alias for i32 multiplication to document spec-level semantics */
spec fn mul_alias(a: i32, b: i32) -> i32 { a * b }
// </vc-helpers>

// <vc-spec>
fn multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use wrapping_mul to avoid overflow while matching i32 multiplication semantics */
    let result = a.wrapping_mul(b);
    result
}
// </vc-code>

}
fn main() {}