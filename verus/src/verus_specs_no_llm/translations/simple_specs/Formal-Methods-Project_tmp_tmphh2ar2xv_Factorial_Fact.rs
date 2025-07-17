// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Fact(x: int) -> y: int
    requires
        x >= 0
;

proof fn lemma_Fact(x: int) -> (y: int)
    requires
        x >= 0
{
    0
}

}