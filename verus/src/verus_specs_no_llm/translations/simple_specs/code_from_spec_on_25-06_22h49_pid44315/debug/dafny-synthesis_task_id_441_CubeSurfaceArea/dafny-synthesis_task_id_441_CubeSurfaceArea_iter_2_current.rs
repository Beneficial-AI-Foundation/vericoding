use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CubeSurfaceArea(size: int) -> (area: int)
    requires
        size > 0,
    ensures
        area == 6 * size * size,
{
    6 * size * size
}

}