// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn UpWhileLess(N: int) -> (i: int)
    requires 0 <= N
    ensures i == N
{
}

}