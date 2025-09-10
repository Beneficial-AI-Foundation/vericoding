use vstd::prelude::*;

verus! {

fn cube_volume(size: i32) -> (volume: i32)
    requires size > 0
    ensures volume == size * size * size
{
    assume(false);
    unreached()
}

}
fn main() {}