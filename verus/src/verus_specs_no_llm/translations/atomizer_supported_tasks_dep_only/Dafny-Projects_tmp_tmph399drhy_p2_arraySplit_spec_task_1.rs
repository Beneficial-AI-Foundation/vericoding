// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ArraySplit(a: Vec<int>) -> b : array<int>, c : array<int>
    ensures
        fresh(b),
        fresh(c),
        a.index(..) == b.index(..) + c.index(..),
        a.len() == b.len() + c.len(),
        a.len() > 1 ==> a.len() > b.len(),
        a.len() > 1 ==> a.len() > c.len()
;

proof fn lemma_ArraySplit(a: Vec<int>) -> (b: Vec<int>, c: Vec<int>)
    ensures
        fresh(b),
        fresh(c),
        a.index(..) == b.index(..) + c.index(..),
        a.len() == b.len() + c.len(),
        a.len() > 1 ==> a.len() > b.len(),
        a.len() > 1 ==> a.len() > c.len()
{
    Vec::new()
}

}