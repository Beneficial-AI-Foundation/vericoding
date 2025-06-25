// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Gauss(n: int) -> (sum: int)
    requires n >= 0
    ensures sum == n*(n+1)/2     //
{
}

}