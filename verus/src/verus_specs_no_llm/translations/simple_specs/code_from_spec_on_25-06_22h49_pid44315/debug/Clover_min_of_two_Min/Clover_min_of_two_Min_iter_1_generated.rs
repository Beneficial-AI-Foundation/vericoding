// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Min(x: int, y: int) -> (z: int)
    ensures
        x<=y ==> z==x,
        x>y ==> z==y
{
    if x <= y {
        x
    } else {
        y
    }
}

}