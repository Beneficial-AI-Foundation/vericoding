// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no-op helper retained to satisfy placeholder */
fn helper_noop() {
    // intentionally empty
}

// </vc-helpers>

// <vc-spec>
fn multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute product directly using built-in multiplication and return */
    let result: i32 = a * b;
    result
}
// </vc-code>

}
fn main() {}