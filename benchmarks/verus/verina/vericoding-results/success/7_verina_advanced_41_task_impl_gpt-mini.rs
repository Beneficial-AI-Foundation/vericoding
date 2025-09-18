// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple max of two integers */
fn max2(a: i32, b: i32) -> (r: i32)
    ensures
        r >= a && r >= b,
        r == a || r == b,
{
    if a >= b { a } else { b }
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
    /* code modified by LLM (iteration 2): compute max of three using max2 and prove properties */
    let r1 = max2(a, b);
    let r2 = max2(r1, c);
    proof {
        // show r2 >= a, r2 >= b, r2 >= c
        assert(r2 >= r1);
        assert(r1 >= a);
        assert(r1 >= b);
        assert(r2 >= c);
        assert(r2 >= a);
        assert(r2 >= b);
        // show r2 is one of a, b, c
        if r2 == r1 {
            assert(r1 == a || r1 == b);
            assert(r2 == a || r2 == b);
        } else {
            assert(r2 == c);
        }
    }
    r2
}
// </vc-code>

}
fn main() {}