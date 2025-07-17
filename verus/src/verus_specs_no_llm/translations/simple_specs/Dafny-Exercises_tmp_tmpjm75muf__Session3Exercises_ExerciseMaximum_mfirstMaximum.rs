// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_mfirstMaximum(v: Vec<int>) -> i:int
    requires
        v.len()>0
    ensures
        0<=i<v.len(),
        forall |k: int| 0<=k<v.len() ==> v.index(i)>=v.index(k),
        forall |l: int| 0<=l<i ==> v.index(i)>v.index(l)
//Algorithm: from left to right
;

proof fn lemma_mfirstMaximum(v: Vec<int>) -> (i: int)
    requires
        v.len()>0
    ensures
        0<=i<v.len(),
        forall |k: int| 0<=k<v.len() ==> v.index(i)>=v.index(k),
        forall |l: int| 0<=l<i ==> v.index(i)>v.index(l)
//Algorithm: from left to right
{
    0
}

}