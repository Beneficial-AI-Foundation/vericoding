// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_PentagonPerimeter(side: int) -> perimeter: int
    requires
        side > 0
    ensures
        perimeter == 5 * side
;

proof fn lemma_PentagonPerimeter(side: int) -> (perimeter: int)
    requires
        side > 0
    ensures
        perimeter == 5 * side
{
    0
}

}