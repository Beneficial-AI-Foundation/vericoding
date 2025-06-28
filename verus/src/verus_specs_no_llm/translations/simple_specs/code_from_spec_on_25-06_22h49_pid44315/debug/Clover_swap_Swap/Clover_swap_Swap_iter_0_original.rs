// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Swap(X: int, Y: int) -> (x: int, y: int)
    ensures
        x==Y,
        y==X
{
    return (0, 0);
}

}