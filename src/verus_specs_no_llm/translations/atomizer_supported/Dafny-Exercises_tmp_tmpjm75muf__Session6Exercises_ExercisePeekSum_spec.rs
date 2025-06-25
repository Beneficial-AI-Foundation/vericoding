// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn mPeekSum(v: Vec<int>) -> (sum: int)
    requires v.len()>0
    ensures sum==peekSum(v,v.len())
 //Implement and verify an O(v.len()) algorithm to solve this problem
{
}

}