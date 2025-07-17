// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_AreaOfLargestTriangleInSemicircle(radius: int) -> area: int
    requires
        radius > 0
    ensures
        area == radius * radius
;

proof fn lemma_AreaOfLargestTriangleInSemicircle(radius: int) -> (area: int)
    requires
        radius > 0
    ensures
        area == radius * radius
{
    0
}

}