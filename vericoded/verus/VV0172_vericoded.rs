// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn pair_swap(a: i32, b: i32) -> (result: (i32, i32))
    ensures
        result.0 == b,
        result.1 == a
{
    (b, a)
}
// </vc-helpers>

// <vc-spec>
fn swap_arithmetic(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == y,
        result.1 == x,
        x != y ==> (result.0 != x && result.1 != y),
// </vc-spec>
// <vc-code>
{
    let r = pair_swap(x, y);
    proof {
        assert(r.0 == y && r.1 == x);
        if x != y {
            assert(r.0 != x);
            assert(r.1 != y);
        }
    }
    r
}
// </vc-code>

}
fn main() {}