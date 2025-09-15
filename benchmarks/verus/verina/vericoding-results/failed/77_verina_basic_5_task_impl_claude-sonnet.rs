// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use correct absolute value syntax */
fn multiply_safe(a: i32, b: i32) -> (result: i32)
    requires (a as int).abs() <= 46340 && (b as int).abs() <= 46340
    ensures result == a * b
{
    a * b
}
// </vc-helpers>

// <vc-spec>
fn multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): direct multiplication since postcondition requires exact result */
    a * b
}
// </vc-code>

}
fn main() {}