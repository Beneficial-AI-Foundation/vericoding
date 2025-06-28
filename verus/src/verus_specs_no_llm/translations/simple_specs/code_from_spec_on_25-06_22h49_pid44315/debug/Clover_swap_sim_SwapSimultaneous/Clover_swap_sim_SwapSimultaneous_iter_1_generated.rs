// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SwapSimultaneous(X: int, Y: int) -> (x: int, y: int)
    ensures
        x==Y,
        y==X
{
    return (Y, X);
}

}