// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_M(x: int) -> seven: int
    ensures
        seven==7
;

proof fn lemma_M(x: int) -> (seven: int)
    ensures
        seven==7
{
    0
}

}