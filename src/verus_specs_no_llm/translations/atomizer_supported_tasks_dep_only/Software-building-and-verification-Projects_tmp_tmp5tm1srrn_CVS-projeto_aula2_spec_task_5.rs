// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn m1(x: int, y: int) -> (z: int)
    requires 0 < x < y
    ensures z >= 0 and z < y and z != x
{
}

}