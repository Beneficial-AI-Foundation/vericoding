// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn swap_simultaneous_ensures(result: (i32, i32), x: i32, y: i32) -> bool {
    result.0 == y && result.1 == x && (x != y ==> result.0 != x && result.1 != y)
}
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
    let pair = (y, x);
    proof {
        assert(pair.0 == y);
        assert(pair.1 == x);
        if x != y {
            assert(pair.0 != x);
            assert(pair.1 != y);
        }
    }
    pair
}
// </vc-code>

}
fn main() {}