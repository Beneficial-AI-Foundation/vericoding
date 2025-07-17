// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_addArrays(a: Vec<int>, b: Vec<int>) -> c : array<int>
    requires
        a.len() == b.len()
    ensures
        b.len() == c.len(),
        forall |i: int| 0 <= i <c.len() ==> c.index(i) == a.index(i) + b.index(i)
;

proof fn lemma_addArrays(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    requires
        a.len() == b.len()
    ensures
        b.len() == c.len(),
        forall |i: int| 0 <= i <c.len() ==> c.index(i) == a.index(i) + b.index(i)
{
    Vec::new()
}

}