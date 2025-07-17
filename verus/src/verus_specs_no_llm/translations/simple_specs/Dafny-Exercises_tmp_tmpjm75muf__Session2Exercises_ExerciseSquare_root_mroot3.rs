// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_mroot3(n: int) -> r:int) //Cost O(log n
    requires
        n>=0
    ensures
        r>=0 && r*r <= n <(r+1)*(r+1)
;

proof fn lemma_mroot3(n: int) -> (r: int) //Cost O(log n)
    requires
        n>=0
    ensures
        r>=0 && r*r <= n <(r+1)*(r+1)
{
    0
}

}