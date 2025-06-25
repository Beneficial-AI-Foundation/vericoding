// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
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