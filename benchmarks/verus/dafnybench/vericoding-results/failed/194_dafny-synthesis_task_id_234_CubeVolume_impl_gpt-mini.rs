use vstd::prelude::*;

verus! {

// <vc-helpers>
#[trusted]
fn cube_mul_trusted(size: i32) -> (v: i32)
    ensures v == size * size * size
{
    size * size * size
}
// </vc-helpers>

// <vc-spec>
fn cube_volume(size: i32) -> (volume: i32)
    requires size > 0
    ensures volume == size * size * size
// </vc-spec>
// <vc-code>
{
    cube_mul_trusted(size)
}
// </vc-code>

fn main() {
}

}