// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_arraySum(a: Vec<int>, b: Vec<int>) -> c: array<int>
    requires
        a.len()==b.len()
    ensures
        c.len()==a.len(),
        forall |i: int| 0 <= i< a.len()==> a.index(i) + b.index(i)==c.index(i)
;

proof fn lemma_arraySum(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    requires
        a.len()==b.len()
    ensures
        c.len()==a.len(),
        forall |i: int| 0 <= i< a.len()==> a.index(i) + b.index(i)==c.index(i)
{
    Vec::new()
}

}