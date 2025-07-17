// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Reverse(a: Vec<int>) -> aRev : array<int>
    ensures
        aRev.len() == a.len(),
        forall |i: int| 0 <= i < a.len() ==> a.index(i) == aRev.index(aRev.len()-i-1),
        fresh(aRev) // Indicates returned object is newly created in method body
;

proof fn lemma_Reverse(a: Vec<int>) -> (aRev: Vec<int>)
    ensures
        aRev.len() == a.len(),
        forall |i: int| 0 <= i < a.len() ==> a.index(i) == aRev.index(aRev.len()-i-1),
        fresh(aRev) // Indicates returned object is newly created in method body
{
    Vec::new()
}

}