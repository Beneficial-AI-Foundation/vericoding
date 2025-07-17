// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_mmaximum2(v: Vec<int>) -> i:int
    requires
        v.len()>0
    ensures
        0<=i<v.len(),
        forall |k: int| 0<=k<v.len() ==> v.index(i)>=v.index(k)
;

proof fn lemma_mmaximum2(v: Vec<int>) -> (i: int)
    requires
        v.len()>0
    ensures
        0<=i<v.len(),
        forall |k: int| 0<=k<v.len() ==> v.index(i)>=v.index(k)
{
    0
}

}