// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn mfirstMaximum(v: Vec<int>) -> (i: int)
    requires v.len()>0
    ensures 0<=i<v.len(),
            forall|k: int| 0<=k<v.len() ==> v[i]>=v[k],
            forall|l: int| 0<=l<i ==> v[i]>v[l]
//Algorithm: from left to right
{
}

}