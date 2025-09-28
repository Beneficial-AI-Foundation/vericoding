use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_cube_bounds(size: i32)
    requires 
        size > 0,
        size <= 1290
    ensures 
        size as int * size as int * size as int <= i32::MAX as int
{
    assert(size <= 1290);
    assert(size as int <= 1290);
    assert(size as int * size as int <= 1290 * 1290);
    assert(1290 * 1290 == 1664100);
    assert(size as int * size as int * size as int <= 1290 * 1290 * 1290);
    assert(1290 * 1290 * 1290 == 2146689000);
    assert(2146689000 <= 2147483647);
    assert(2147483647 == i32::MAX as int);
}
// </vc-helpers>

// <vc-spec>
fn cube_volume(size: i32) -> (volume: i32)
    requires size > 0
    ensures volume == size * size * size
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_cube_bounds(size);
    }
    let temp = size * size;
    temp * size
}
// </vc-code>

fn main() {
}

}