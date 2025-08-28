use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue was a syntax error in the code section
// </vc-helpers>

// <vc-spec>
// <vc-spec>
proof fn abs(x: int) -> (y: int)
    ensures 
        x >= 0 ==> x == y,
        x < 0 ==> x + y == 0,
// </vc-spec>
// </vc-spec>

// <vc-code>
proof fn abs(x: int) -> (y: int)
    ensures
        x >= 0 ==> x == y,
        x < 0 ==> x + y == 0
{
    if x >= 0 {
        x
    } else {
        -x
    }
}
// </vc-code>

fn main() {
}

}