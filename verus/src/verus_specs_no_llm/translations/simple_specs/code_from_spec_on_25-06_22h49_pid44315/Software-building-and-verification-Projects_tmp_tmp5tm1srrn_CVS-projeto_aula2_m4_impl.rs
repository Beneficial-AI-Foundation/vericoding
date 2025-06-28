// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn m4(x: int, y: int) -> (z: bool)
    ensures
        z ==> x==y && x==y ==> z
{
    x == y
}

}