// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn countMin(v: Vec<int>, x: int, i: int) -> int
 reads v
    requires
        0<=i<=v.len()
    ensures
        !(x in v.index(0..i)) ==> countMin(v,x,i)==0
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