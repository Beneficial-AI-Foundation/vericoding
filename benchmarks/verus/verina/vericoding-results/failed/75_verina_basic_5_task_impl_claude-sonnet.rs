// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add helper to check multiplication safety */
fn can_multiply_safely(a: i32, b: i32) -> bool {
    a.checked_mul(b).is_some()
}
// </vc-helpers>

// <vc-spec>
fn multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use direct multiplication since spec requires exact result */
    a * b
}
// </vc-code>

}
fn main() {}