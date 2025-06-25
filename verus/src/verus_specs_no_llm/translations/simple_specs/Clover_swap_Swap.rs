// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
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