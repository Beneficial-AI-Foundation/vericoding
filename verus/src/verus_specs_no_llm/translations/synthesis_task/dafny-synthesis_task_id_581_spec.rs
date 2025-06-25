// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SquarePyramidSurfaceArea(baseEdge: int, height: int) -> (area: int)
    requires
        baseEdge > 0,
        height > 0
    ensures
        area == baseEdge * baseEdge + 2 * baseEdge * height
{
    return 0;
}

}