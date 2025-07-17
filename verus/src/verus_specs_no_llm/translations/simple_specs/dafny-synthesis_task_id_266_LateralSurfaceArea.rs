// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_LateralSurfaceArea(size: int) -> area: int
    requires
        size > 0
    ensures
        area == 4 * size * size
;

proof fn lemma_LateralSurfaceArea(size: int) -> (area: int)
    requires
        size > 0
    ensures
        area == 4 * size * size
{
    0
}

}