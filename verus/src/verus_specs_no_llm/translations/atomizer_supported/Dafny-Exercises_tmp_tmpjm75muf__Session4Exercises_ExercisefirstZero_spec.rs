// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_mfirstCero(v: Vec<int>) -> i:int
    ensures
        0 <=i<=v.len(),
        forall |j: int| 0<=j<i ==> v.index(j)!=0,
        i!=v.len() ==> v.index(i)==0
;

proof fn lemma_mfirstCero(v: Vec<int>) -> (i: int)
    ensures
        0 <=i<=v.len(),
        forall |j: int| 0<=j<i ==> v.index(j)!=0,
        i!=v.len() ==> v.index(i)==0
{
    0
}

}