// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SwapBitvectors(X: bv8, Y: bv8) -> x: bv8, y: bv8
    ensures x==Y,
            y==X
{
}

}