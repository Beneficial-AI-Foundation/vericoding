// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CubeVolume(size: int) -> volume: int
    requires
        size > 0
    ensures
        volume == size * size * size
;

proof fn lemma_CubeVolume(size: int) -> (volume: int)
    requires
        size > 0
    ensures
        volume == size * size * size
{
    0
}

}