// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Add(x: int, y: int) -> r: int
    ensures
        r == x+y
;

proof fn lemma_Add(x: int, y: int) -> (r: int)
    ensures
        r == x+y
{
    0
}

}