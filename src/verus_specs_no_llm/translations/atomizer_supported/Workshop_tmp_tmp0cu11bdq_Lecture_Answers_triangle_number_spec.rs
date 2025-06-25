// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn TriangleNumber(N: int) -> (t: int)
    requires N >= 0
    ensures t == N * (N + 1) / 2
{
}

}