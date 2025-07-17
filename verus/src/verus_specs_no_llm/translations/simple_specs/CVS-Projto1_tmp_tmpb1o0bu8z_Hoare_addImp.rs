// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn add(l: List<int>) -> int
{
    0
}

spec fn spec_addImp(l: List<int>) -> s: int
    ensures
        s == add(l)
;

proof fn lemma_addImp(l: List<int>) -> (s: int)
    ensures
        s == add(l)
{
    0
}

}