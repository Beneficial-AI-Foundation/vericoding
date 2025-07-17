// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_problem2(p: int, q: int, X: int, Y: int) -> r:int, s:int
    requires
        p == 2*X + Y && q == X + 3
    ensures
        r == X && s == Y
;

proof fn lemma_problem2(p: int, q: int, X: int, Y: int) -> (r: int, s: int)
    requires
        p == 2*X + Y && q == X + 3
    ensures
        r == X && s == Y
{
    (0, 0)
}

}