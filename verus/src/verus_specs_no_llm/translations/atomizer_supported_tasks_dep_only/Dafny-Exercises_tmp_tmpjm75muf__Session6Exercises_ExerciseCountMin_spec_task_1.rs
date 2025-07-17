// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn min(v: Vec<int>, i: int) -> int
 reads v
    requires
        1<=i<=v.len()
    ensures
        forall |k: int|0<=k<i==> v.index(k)>=min(v,i)
{
    0
}

spec fn spec_mCountMin(v: Vec<int>) -> c:int
    requires
        v.len()>0
    ensures
        c==countMin(v,min(v,v.len()),v.len())
//Implement && verify an O(v.len()) algorithm
;

proof fn lemma_mCountMin(v: Vec<int>) -> (c: int)
    requires
        v.len()>0
    ensures
        c==countMin(v,min(v,v.len()),v.len())
//Implement && verify an O(v.len()) algorithm
{
    0
}

}