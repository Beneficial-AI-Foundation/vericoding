// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SwapBitvectors(X: bv8, Y: bv8) -> (x: bv8, y: bv8)
    ensures
        x==Y,
        y==X
{
    return (Y, X);
}

}