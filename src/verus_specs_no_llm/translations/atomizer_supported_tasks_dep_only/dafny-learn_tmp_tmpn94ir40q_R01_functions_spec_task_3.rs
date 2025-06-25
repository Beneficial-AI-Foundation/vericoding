// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Abs(x: int) -> (y: int)
    ensures abs(x) == y
{
}

}