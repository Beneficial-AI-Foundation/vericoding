// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn MultipleReturns(x: int, y: int) -> more: int, less: int
    requires 0 < y
    ensures less < x < more
{
}

}