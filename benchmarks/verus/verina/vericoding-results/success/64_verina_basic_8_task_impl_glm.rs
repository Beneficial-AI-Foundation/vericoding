// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added postconditions */
fn min(a: i32, b: i32) -> (result: i32)
    ensures
        result <= a && result <= b,
        result == a || result == b,
{
    if a < b {
        a
    } else {
        b
    }
}
// </vc-helpers>

// <vc-spec>
fn my_min(a: i32, b: i32) -> (result: i32)
    ensures
        result <= a && result <= b,
        result == a || result == b,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): using helper with postconditions */
{
    let result = min(a, b);
    result
}
// </vc-code>

}
fn main() {}