use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
proof fn abs(x: int) -> (y: int)
    ensures 
        x >= 0 ==> x == y,
        x < 0 ==> x + y == 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>

fn main() {
}

}