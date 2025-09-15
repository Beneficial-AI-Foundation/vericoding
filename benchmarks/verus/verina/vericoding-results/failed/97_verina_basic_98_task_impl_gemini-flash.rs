// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn triple_spec(x: i32) -> i32 { x * 3 }
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
{
    let result = x * 3;

    assert(result / 3 == x) by {
        assert(x * 3 / 3 == x);
    };
    assert(result / 3 * 3 == result) by {
        assert(x * 3 / 3 * 3 == x * 3);
    };
    result
}
// </vc-code>

}
fn main() {}