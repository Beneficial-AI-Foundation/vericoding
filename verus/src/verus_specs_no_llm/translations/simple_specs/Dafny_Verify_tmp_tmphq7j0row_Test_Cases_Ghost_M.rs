// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_M() -> r: int
    ensures
        r == 29
;

proof fn lemma_M() -> (r: int)
    ensures
        r == 29
{
    0
}

}