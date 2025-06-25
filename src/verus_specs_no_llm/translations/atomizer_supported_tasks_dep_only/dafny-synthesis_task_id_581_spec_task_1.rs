// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SquarePyramidSurfaceArea(baseEdge: int, height: int) -> (area: int)
    requires baseEdge > 0,
             height > 0
    ensures area == baseEdge * baseEdge + 2 * baseEdge * height
{
}

}