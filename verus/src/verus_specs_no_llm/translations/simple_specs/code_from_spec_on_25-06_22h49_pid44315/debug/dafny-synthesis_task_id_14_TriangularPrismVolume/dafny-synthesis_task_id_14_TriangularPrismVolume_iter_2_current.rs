// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TriangularPrismVolume(base: int, height: int, length: int) -> (volume: int)
    requires
        base > 0,
        height > 0,
        length > 0
    ensures
        volume == (base * height * length) / 2
{
    (base * height * length) / 2
}

}