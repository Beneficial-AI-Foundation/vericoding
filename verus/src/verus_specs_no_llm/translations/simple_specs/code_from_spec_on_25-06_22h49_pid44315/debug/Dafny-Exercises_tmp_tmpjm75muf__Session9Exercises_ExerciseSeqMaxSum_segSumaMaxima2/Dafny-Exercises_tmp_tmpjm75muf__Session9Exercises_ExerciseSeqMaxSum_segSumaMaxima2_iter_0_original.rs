// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn segSumaMaxima2(v: Vec<int>, i: int) -> (s: int, k: int)
    requires
        v.len()>0 && 0<=i<v.len()
    ensures
        0<=k<=i && s==Sum2(v,k,i+1) && SumMaxToRight2(v,0,i,s)
//Implement && verify
{
    return (0, 0);
}

}