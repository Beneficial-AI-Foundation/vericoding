// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_mlastMaximum(v: Vec<int>) -> i:int
    requires
        v.len()>0
    ensures
        0<=i<v.len(),
        forall |k: int| 0<=k<v.len() ==> v.index(i)>=v.index(k),
        forall |l: int| i<l<v.len() ==> v.index(i)>v.index(l)
;

proof fn lemma_mlastMaximum(v: Vec<int>) -> (i: int)
    requires
        v.len()>0
    ensures
        0<=i<v.len(),
        forall |k: int| 0<=k<v.len() ==> v.index(i)>=v.index(k),
        forall |l: int| i<l<v.len() ==> v.index(i)>v.index(l)
{
    0
}

}