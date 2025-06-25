// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SumIntsLoop(n: int) -> (s: int)
    requires n >= 0;
    ensures s == sumInts(n),
            s == n*(n+1)/2;
{
}

}