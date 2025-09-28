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
    let volume = size * size * size;
    volume
}
// </vc-code>

fn main() {
}

}