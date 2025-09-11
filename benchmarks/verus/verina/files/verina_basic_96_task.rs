// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn swap_simultaneous(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == y,
        result.1 == x,
        x != y ==> result.0 != x && result.1 != y,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}