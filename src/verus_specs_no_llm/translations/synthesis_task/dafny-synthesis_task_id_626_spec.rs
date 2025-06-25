// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn AreaOfLargestTriangleInSemicircle(radius: int) -> (area: int)
    requires radius > 0
    ensures area == radius * radius
{
}

}