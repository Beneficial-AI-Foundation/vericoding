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

fn m4(x: int, y: int) -> (z: bool)
    ensures
        z ==> x==y && x==y ==> z
{
    return false;
}

}