// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AreaOfLargestTriangleInSemicircle(radius: int) -> (area: int)
    requires
        radius > 0
    ensures
        area == radius * radius
{
    return 0;
}

}