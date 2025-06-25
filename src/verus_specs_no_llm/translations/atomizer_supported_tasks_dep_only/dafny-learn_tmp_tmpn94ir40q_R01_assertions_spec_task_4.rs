// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Max(a: int, b: int) -> (c: int)
    ensures c >= a,
            c >= b
{
}

}