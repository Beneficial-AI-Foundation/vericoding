// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn TriangularPrismVolume(base: int, height: int, length: int) -> (volume: int)
    requires base > 0,
             height > 0,
             length > 0
    ensures volume == (base * height * length) / 2
{
}

}