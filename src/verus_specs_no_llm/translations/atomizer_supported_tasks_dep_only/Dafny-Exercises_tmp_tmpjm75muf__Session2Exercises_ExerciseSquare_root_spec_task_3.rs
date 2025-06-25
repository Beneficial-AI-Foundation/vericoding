// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn mroot3(n: int) -> (r: int) //Cost O(log n)
    requires n>=0
    ensures r>=0 and r*r <= n <(r+1)*(r+1)
{
}

}