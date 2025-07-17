// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_SquarePerimeter(side: int) -> perimeter: int
    requires
        side > 0
    ensures
        perimeter == 4 * side
;

proof fn lemma_SquarePerimeter(side: int) -> (perimeter: int)
    requires
        side > 0
    ensures
        perimeter == 4 * side
{
    0
}

}