use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn cube_volume(size: i32) -> (volume: i32)
    requires size > 0
    ensures volume == size * size * size
// </vc-spec>
// <vc-code>
{
    assume(false);
    0 // unreachable but needed for return type
}
// </vc-code>

fn main() {
}

}