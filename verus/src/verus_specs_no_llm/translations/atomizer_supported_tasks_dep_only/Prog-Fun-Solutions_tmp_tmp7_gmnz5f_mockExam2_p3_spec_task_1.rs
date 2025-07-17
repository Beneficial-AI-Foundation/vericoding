// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_problem3(m: int, X: int) -> r:int
    requires
        X >= 0 && (2*m == 1 - X || m == X + 3)
    ensures
        r == X
;

proof fn lemma_problem3(m: int, X: int) -> (r: int)
    requires
        X >= 0 && (2*m == 1 - X || m == X + 3)
    ensures
        r == X
{
    0
}

}