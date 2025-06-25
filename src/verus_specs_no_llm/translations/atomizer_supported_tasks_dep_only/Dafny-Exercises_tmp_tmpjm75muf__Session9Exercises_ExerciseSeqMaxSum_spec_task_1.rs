// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn SumMaxToRight(v: Vec<int>, i: int, s: int)
reads v
requires 0<=i<v.Length
{
forall l, ss {: induction l}::0<=l<=i && ss==i+1==> Sum(v, l, ss)<=s
}


// SPEC 

method segMaxSum(v: Vec<int>, i: int) returns (s:int, k: int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum(v, k, i+1) &&  SumMaxToRight(v, i, s) -> bool {
    
}

fn segMaxSum(v: Vec<int>, i: int) -> s: int, k: int
    requires v.len()>0 and 0<=i<v.len()
    ensures 0<=k<=i and s==Sum(v,k,i+1) and  SumMaxToRight(v,i,s)
{
}

}