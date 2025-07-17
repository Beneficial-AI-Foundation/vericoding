// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_add_by_one(x: int, y: int) -> r:int
    requires
        y >= 0
    ensures
        r == x + y
;

proof fn lemma_add_by_one(x: int, y: int) -> (r: int)
    requires
        y >= 0
    ensures
        r == x + y
{
    0
}

}