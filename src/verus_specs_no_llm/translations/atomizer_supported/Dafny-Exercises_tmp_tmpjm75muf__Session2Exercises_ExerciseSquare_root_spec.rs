// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn mroot1(n: int) -> (r: int) //Cost O(root n)
    requires n>=0
    ensures r>=0 and r*r <= n <(r+1)*(r+1)
{
}

}