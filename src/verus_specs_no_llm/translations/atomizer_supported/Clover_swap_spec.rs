// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Swap(X: int, Y: int) -> x: int, y: int
    ensures x==Y,
            y==X
{
}

}