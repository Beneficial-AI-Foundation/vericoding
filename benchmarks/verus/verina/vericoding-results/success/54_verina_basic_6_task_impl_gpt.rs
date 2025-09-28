// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min2(x: i32, y: i32) -> (r: i32)
    ensures
        r <= x && r <= y,
        r == x || r == y
{
    if x <= y { x } else { y }
}
// </vc-helpers>

// <vc-spec>
fn min_of_three(a: i32, b: i32, c: i32) -> (result: i32)
    ensures
        result <= a && result <= b && result <= c,
        result == a || result == b || result == c,
// </vc-spec>
// <vc-code>
{
    let m = min2(a, b);
    let r = min2(m, c);

    // Facts from min2's ensures
    assert(r <= m && r <= c);
    assert(r == m || r == c);
    assert(m <= a && m <= b);
    assert(m == a || m == b);

    // Derive r <= a and r <= b via transitivity
    assert(r <= a);
    assert(r <= b);

    // Show r is one of a, b, or c
    proof {
        if r == c {
            assert(r == a || r == b || r == c);
        } else {
            assert(r == m);
            if m == a {
                assert(r == a || r == b || r == c);
            } else {
                assert(m == b);
                assert(r == a || r == b || r == c);
            }
        }
    }

    r
}
// </vc-code>

}
fn main() {}