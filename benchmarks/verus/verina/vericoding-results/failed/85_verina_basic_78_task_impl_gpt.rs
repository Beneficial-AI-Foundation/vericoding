// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn add_int(a: int, b: int) -> int { a + b }
spec fn sub_int(a: int, b: int) -> int { a - b }
proof fn lemma_add_sub_cancel(x: int, y: int)
    ensures sub_int(add_int(x, y), y) == x
{ }
// </vc-helpers>

// <vc-spec>
fn multiple_returns(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == x + y,
        result.1 + y == x,
// </vc-spec>
// <vc-code>
{
    let s: i32 = x + y;
    let d: i32 = x - y;
    (s, d)
}
// </vc-code>

}
fn main() {}