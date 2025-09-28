// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn min(a: int, b: int) -> (result: int)
    ensures
        result <= a && result <= b,
        result == a || result == b
{
    if a < b {
        a
    } else {
        b
    }
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
    proof {
        let x = min(a as int, b as int);
        let y = min(x, c as int);
        assert(y <= a as int && y <= b as int && y <= c as int) by {
            assert(y <= x && x <= a && x <= b);
        }
        assert(y == a as int || y == b as int || y == c as int) by {
            if y == x {
                if x == a as int {
                    assert(y == a as int);
                } else {
                    assert(x == b as int);
                    assert(y == b as int);
                }
            } else {
                assert(y == c as int);
            }
        }
    }
    
    let result = if a <= b {
        if a <= c { a } else { c }
    } else {
        if b <= c { b } else { c }
    };
    result
}
// </vc-code>

}
fn main() {}