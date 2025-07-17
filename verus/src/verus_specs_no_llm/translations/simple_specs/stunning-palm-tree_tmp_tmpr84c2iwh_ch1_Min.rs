// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Min(x: int, y: int) -> r: int
    ensures
        r <= x && r <= y,
        r == x || r == y
;

proof fn lemma_Min(x: int, y: int) -> (r: int)
    ensures
        r <= x && r <= y,
        r == x || r == y
{
    0
}

}