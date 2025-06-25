// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ComputeAvg(a: int, b: int) -> (avg: int)
    ensures avg == (a+b)/2
{
}

}