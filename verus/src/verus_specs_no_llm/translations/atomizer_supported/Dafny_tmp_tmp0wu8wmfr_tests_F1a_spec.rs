// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_F() -> r: int
    ensures
        r <= 0
;

proof fn lemma_F() -> (r: int)
    ensures
        r <= 0
{
    0
}

}