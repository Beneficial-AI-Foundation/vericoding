// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ArraySum(a: Vec<int>, b: Vec<int>) -> c : array<int>
    requires
        a.len() == b.len()
    ensures
        c.len() == a.len() && 
    forall |i: int| 0 <= i < c.len() ==> c.index(i) == a.index(i) + b.index(i) // TODO
;

proof fn lemma_ArraySum(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    requires
        a.len() == b.len()
    ensures
        c.len() == a.len() && 
    forall |i: int| 0 <= i < c.len() ==> c.index(i) == a.index(i) + b.index(i) // TODO
{
    Vec::new()
}

}