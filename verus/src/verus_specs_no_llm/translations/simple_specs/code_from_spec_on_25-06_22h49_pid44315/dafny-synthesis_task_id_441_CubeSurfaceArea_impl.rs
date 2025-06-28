use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn CubeSurfaceArea(size: int) -> int
    requires
        size > 0,
    ensures
        CubeSurfaceArea(size) == 6 * size * size,
{
    6 * size * size
}

}