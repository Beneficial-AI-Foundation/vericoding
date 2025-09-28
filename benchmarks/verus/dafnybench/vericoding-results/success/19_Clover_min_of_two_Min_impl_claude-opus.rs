use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min(x: int, y: int) -> (z: int)
    ensures
        x <= y ==> z == x,
        x > y ==> z == y,
// </vc-spec>
// <vc-code>
{
    if x <= y {
        x
    } else {
        y
    }
}
// </vc-code>

fn main() {}

}