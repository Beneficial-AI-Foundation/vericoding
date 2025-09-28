// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn min2(a: i32, b: i32) -> i32 {
    if a <= b { a } else { b }
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
    let result = if a <= b {
        if a <= c { a } else { c }
    } else {
        if b <= c { b } else { c }
    };
    proof {
        if a <= b {
            if a <= c {
                assert(result == a);
                assert(result <= a && result <= b && result <= c);
            } else {
                assert(result == c);
                assert(result <= a && result <= b && result <= c);
            }
        } else {
            if b <= c {
                assert(result == b);
                assert(result <= a && result <= b && result <= c);
            } else {
                assert(result == c);
                assert(result <= a && result <= b && result <= c);
            }
        }
    }
    result
}
// </vc-code>

}
fn main() {}