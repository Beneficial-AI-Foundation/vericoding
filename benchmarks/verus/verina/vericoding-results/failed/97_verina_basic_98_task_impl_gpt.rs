// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn triple_helper(x: i32) -> i32 { let a = x + x; a + x }
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
{
    let result = triple_helper(x);
    result
}
// </vc-code>

}
fn main() {}