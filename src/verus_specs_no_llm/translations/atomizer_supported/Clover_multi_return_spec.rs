// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn MultipleReturns(x: int, y: int) -> more: int, less: int
    ensures more == x+y,
            less == x-y
{
}

}