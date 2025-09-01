use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn abs(x: i32) -> (result: i32)
    // pre-conditions-start
    requires
        x != i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result >= 0,
        result == x || result == -x,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if x >= 0 {
        let r: i32 = x;
        proof {
            assert(r >= 0);
            assert(r == x || r == -x);
        }
        r
    } else {
        let r: i32 = -x;
        proof {
            // from branch we have x < 0, and precondition ensures x != i32::MIN,
            // so negation is safe and yields a non-negative value
            assert(x < 0);
            assert(x != i32::MIN);
            assert(r >= 0);
            assert(r == x || r == -x);
        }
        r
    }
}
// </vc-code>

fn main() {}
}