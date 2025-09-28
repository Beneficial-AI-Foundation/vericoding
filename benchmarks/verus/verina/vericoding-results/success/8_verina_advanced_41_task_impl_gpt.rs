// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn max2_exec(x: i32, y: i32) -> (r: i32)
    ensures
        r >= x && r >= y,
        r == x || r == y
{
    if x >= y {
        x
    } else {
        y
    }
}
// </vc-helpers>

// <vc-spec>
fn max_of_three(a: i32, b: i32, c: i32) -> (result: i32)
    ensures
        result >= a && result >= b && result >= c,
        result == a || result == b || result == c,
// </vc-spec>
// <vc-code>
{
    let m = max2_exec(a, b);
    let r = max2_exec(m, c);
    proof {
        // From postconditions of max2_exec calls
        assert(r >= a);
        assert(r >= b);
        assert(r >= c);
        assert(r == m || r == c);
        assert(m == a || m == b);
        if r == m {
            if m == a {
                assert(r == a);
            } else {
                assert(m == b);
                assert(r == b);
            }
        } else {
            assert(r == c);
        }
    }
    r
}
// </vc-code>

}
fn main() {}