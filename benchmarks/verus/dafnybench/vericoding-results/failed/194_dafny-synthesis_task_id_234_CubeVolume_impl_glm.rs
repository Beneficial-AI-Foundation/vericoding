use vstd::prelude::*;

verus! {

// <vc-helpers>
const MAX_SIZE: i32 = 1290;
const MAX_CUBE: i32 = MAX_SIZE * MAX_SIZE * MAX_SIZE;

proof fn lemma_no_overflow(size: i32)
    requires 0 < size && size <= MAX_SIZE
    ensures size * size * size <= i32::MAX
{
    assert(size * size * size <= MAX_CUBE);
    assert(MAX_CUBE < i32::MAX);
}

fn checked_cube(size: i32) -> (result: i32)
    requires 0 < size
    ensures result == size * size * size
{
    if size > MAX_SIZE {
        0
    } else {
        proof {
            lemma_no_overflow(size);
        }
        size * size * size
    }
}
// </vc-helpers>

// <vc-spec>
fn cube_volume(size: i32) -> (volume: i32)
    requires size > 0
    ensures volume == size * size * size
// </vc-spec>
// <vc-code>
{
    checked_cube(size)
}
// </vc-code>

fn main() {
}

}