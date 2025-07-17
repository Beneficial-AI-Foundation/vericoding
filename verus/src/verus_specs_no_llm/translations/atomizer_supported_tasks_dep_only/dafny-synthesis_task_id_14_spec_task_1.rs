// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_TriangularPrismVolume(base: int, height: int, length: int) -> volume: int
    requires
        base > 0,
        height > 0,
        length > 0
    ensures
        volume == (base * height * length) / 2
;

proof fn lemma_TriangularPrismVolume(base: int, height: int, length: int) -> (volume: int)
    requires
        base > 0,
        height > 0,
        length > 0
    ensures
        volume == (base * height * length) / 2
{
    0
}

}