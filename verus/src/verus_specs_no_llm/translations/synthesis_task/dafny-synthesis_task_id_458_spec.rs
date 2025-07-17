// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_RectangleArea(length: int, width: int) -> area: int
    requires
        length > 0,
        width > 0
    ensures
        area == length * width
;

proof fn lemma_RectangleArea(length: int, width: int) -> (area: int)
    requires
        length > 0,
        width > 0
    ensures
        area == length * width
{
    0
}

}