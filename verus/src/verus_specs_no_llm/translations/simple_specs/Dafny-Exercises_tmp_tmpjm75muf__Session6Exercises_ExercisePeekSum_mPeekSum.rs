// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn peekSum(v: Vec<int>, i: int) -> int
 reads v
    requires
        0<=i<=v.len()
{
    0
}

spec fn spec_mPeekSum(v: Vec<int>) -> sum:int
    requires
        v.len()>0
    ensures
        sum==peekSum(v,v.len())
 //Implement && verify an O(v.len()) algorithm to solve this problem
;

proof fn lemma_mPeekSum(v: Vec<int>) -> (sum: int)
    requires
        v.len()>0
    ensures
        sum==peekSum(v,v.len())
 //Implement && verify an O(v.len()) algorithm to solve this problem
{
    0
}

}