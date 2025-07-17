// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_plus_one(x: int) -> r:int
    requires
        x >= 0
    ensures
        r == x + 1
;

proof fn lemma_plus_one(x: int) -> (r: int)
    requires
        x >= 0
    ensures
        r == x + 1
{
    0
}

}