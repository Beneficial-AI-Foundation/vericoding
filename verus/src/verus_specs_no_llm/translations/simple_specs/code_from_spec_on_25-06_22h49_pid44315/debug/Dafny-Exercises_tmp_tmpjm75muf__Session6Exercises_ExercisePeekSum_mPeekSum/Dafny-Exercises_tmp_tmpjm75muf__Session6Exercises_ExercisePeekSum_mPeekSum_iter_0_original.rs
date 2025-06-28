// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mPeekSum(v: Vec<int>) -> (sum: int)
    requires
        v.len()>0
    ensures
        sum==peekSum(v,v.len())
 //Implement && verify an O(v.len()) algorithm to solve this problem
{
    return 0;
}

}