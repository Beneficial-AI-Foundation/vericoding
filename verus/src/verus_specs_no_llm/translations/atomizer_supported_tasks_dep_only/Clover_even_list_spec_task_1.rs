// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_FindEvenNumbers(arr: Vec<int>) -> evenNumbers: array<int>
    ensures
        forall x
;

proof fn lemma_FindEvenNumbers(arr: Vec<int>) -> (evenNumbers: Vec<int>)
    ensures
        forall x
{
    Vec::new()
}

}