// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sum2(v: Vec<int>, i: int, j: int) -> int
reads v
    requires
        0<=i<=j<=v.len()
{
    0
}

spec fn spec_segSumaMaxima2(v: Vec<int>, i: int) -> s:int,k:int
    requires
        v.len()>0 && 0<=i<v.len()
    ensures
        0<=k<=i && s==Sum2(v,k,i+1) &&  SumMaxToRight2(v,0,i,s)
//Implement && verify
;

proof fn lemma_segSumaMaxima2(v: Vec<int>, i: int) -> (s: int, k: int)
    requires
        v.len()>0 && 0<=i<v.len()
    ensures
        0<=k<=i && s==Sum2(v,k,i+1) &&  SumMaxToRight2(v,0,i,s)
//Implement && verify
{
    (0, 0)
}

}