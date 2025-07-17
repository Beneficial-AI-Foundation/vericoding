// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CubeSurfaceArea(size: int) -> area: int
    requires
        size > 0
    ensures
        area == 6 * size * size
;

proof fn lemma_CubeSurfaceArea(size: int) -> (area: int)
    requires
        size > 0
    ensures
        area == 6 * size * size
{
    0
}

}