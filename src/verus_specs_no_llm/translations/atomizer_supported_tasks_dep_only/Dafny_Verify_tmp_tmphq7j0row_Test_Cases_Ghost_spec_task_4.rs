// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn MyMethod(x: int) -> (y: int)
    requires 10 <= x
    ensures 25 <= y
{
}

}