// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(x: int, y: int) -> (a: int)
    ensures
        a == x || a == y,
        x > y ==> a == x,
        x <= y ==> a == y
{
    if x > y {
        x
    } else {
        y
    }
}

}