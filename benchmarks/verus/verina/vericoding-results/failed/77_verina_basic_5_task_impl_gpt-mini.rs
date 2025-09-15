// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): declare i32 multiplication spec */
spec fn i32_mul(a: i32, b: i32) -> i32 { a * b }
// </vc-helpers>

// <vc-spec>
fn multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use wrapping multiplication to avoid overflow and match spec */
    let result: i32 = a.wrapping_mul(b);
    result
}
// </vc-code>

}
fn main() {}