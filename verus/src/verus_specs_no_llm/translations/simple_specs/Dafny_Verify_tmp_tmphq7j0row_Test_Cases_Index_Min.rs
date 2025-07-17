// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Min(x: int, y: int) -> m: int
    ensures
        m <= x && m <= y,
        m == x || m == y
;

proof fn lemma_Min(x: int, y: int) -> (m: int)
    ensures
        m <= x && m <= y,
        m == x || m == y
{
    0
}

}