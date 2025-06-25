// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn PlusOne(x: int) -> (y: int)
    requires x >= 0
    ensures y > 0
{
}

}