// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn m4(x: int, y: int) -> (z: bool)
    ensures z ==> x==y and x==y ==> z
{
}

}