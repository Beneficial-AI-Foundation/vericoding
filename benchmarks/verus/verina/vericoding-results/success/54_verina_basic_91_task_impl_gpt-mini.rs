// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
pub proof fn neq_sym(x: i32, y: i32)
    ensures
        x != y ==> y != x,
{
    if x != y {
        assert(y != x);
    }
}
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
    let result: (i32, i32) = (y, x);
    proof {
        assert(result.0 == y);
        assert(result.1 == x);
        if x != y {
            assert(result.0 != x && result.1 != y);
        }
    }
    result
}
// </vc-code>

}
fn main() {}