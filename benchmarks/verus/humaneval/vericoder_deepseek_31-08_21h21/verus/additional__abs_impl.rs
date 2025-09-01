use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn abs_proof(x: int)
    requires
        x != i32::MIN as int,
    ensures
        (if x >= 0 { x } else { -x }) >= 0,
        (if x >= 0 { x } else { -x }) == x || (if x >= 0 { x } else { -x }) == -x
{
}
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
        proof { abs_proof(x as int); }
        x
    } else {
        let result = -x;
        proof { abs_proof(x as int); }
        result
    }
}
// </vc-code>

fn main() {}
}