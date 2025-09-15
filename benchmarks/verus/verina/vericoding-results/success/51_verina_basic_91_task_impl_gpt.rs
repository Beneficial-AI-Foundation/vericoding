// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn swap_pair(x: i32, y: i32) -> (i32, i32) { (y, x) }
proof fn lemma_swap_correct(x: i32, y: i32)
    ensures
        swap_pair(x, y).0 == y,
        swap_pair(x, y).1 == x,
        x != y ==> swap_pair(x, y).0 != x && swap_pair(x, y).1 != y
{ }
// </vc-helpers>

// <vc-spec>
fn swap(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == y,
        result.1 == x,
        x != y ==> result.0 != x && result.1 != y,
// </vc-spec>
// <vc-code>
{
    (y, x)
}
// </vc-code>

}
fn main() {}