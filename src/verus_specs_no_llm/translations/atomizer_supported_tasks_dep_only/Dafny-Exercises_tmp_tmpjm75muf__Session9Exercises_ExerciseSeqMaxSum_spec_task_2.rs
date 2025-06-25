// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn segSumaMaxima2(v: Vec<int>, i: int) -> s: int, k: int
    requires v.len()>0 and 0<=i<v.len()
    ensures 0<=k<=i and s==Sum2(v,k,i+1) and  SumMaxToRight2(v,0,i,s)
//Implement and verify
{
}

}