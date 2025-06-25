// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Max(x: int, y: int) -> (a: int)
    ensures a == x or a == y;,
            x > y ==> a == x;,
            x <= y ==> a == y;
{
}

}