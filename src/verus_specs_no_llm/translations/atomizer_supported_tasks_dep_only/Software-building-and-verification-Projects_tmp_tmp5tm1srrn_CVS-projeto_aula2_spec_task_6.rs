// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn m2(x: nat) -> (y: int)
    requires x <= -1
    ensures y > x and y < x
{
}

}