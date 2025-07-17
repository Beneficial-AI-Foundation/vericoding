// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Main() -> x: int, y: int
    ensures
        x == y
;

proof fn lemma_Main() -> (x: int, y: int)
    ensures
        x == y
{
    (0, 0)
}

}