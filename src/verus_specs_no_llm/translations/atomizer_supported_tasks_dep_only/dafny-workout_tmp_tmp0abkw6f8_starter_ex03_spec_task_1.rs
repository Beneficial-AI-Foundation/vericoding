// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Abs(x: int) -> (y: int)
    requires x == -1
    ensures 0 <= y,
            0 <= x ==> y == x,
            x < 0 ==> y == -x
{
}

}