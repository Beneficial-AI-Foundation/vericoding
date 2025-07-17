// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_concat(a: Vec<int>, b: Vec<int>) -> c:array<int>
    ensures
        c.len()==b.len()+a.len(),
        forall |k: int| 0 <= k < a.len() ==> c.index(k) == a.index(k),
        forall |k: int| 0 <= k < b.len() ==> c.index(k+a.len()) == b.index(k)
;

proof fn lemma_concat(a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    ensures
        c.len()==b.len()+a.len(),
        forall |k: int| 0 <= k < a.len() ==> c.index(k) == a.index(k),
        forall |k: int| 0 <= k < b.len() ==> c.index(k+a.len()) == b.index(k)
{
    Vec::new()
}

}