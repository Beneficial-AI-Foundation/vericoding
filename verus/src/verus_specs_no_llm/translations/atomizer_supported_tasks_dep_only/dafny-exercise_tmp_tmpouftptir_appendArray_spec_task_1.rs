// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_appendArray(a: Vec<int>, b: Vec<int>) -> c: array<int>
    ensures
        c.len() == a.len() + b.len(),
        forall |i: int| 0 <= i < a.len() ==> a.index(i) == c.index(i),
        forall |i: int| 0 <= i < b.len() ==> b.index(i) == c.index(a.len() + i)
;

proof fn lemma_appendArray(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    ensures
        c.len() == a.len() + b.len(),
        forall |i: int| 0 <= i < a.len() ==> a.index(i) == c.index(i),
        forall |i: int| 0 <= i < b.len() ==> b.index(i) == c.index(a.len() + i)
{
    Vec::new()
}

}