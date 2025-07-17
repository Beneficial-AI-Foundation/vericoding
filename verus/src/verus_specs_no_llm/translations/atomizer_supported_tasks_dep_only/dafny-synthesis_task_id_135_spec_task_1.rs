// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_NthHexagonalNumber(n: int) -> hexNum: int
    requires
        n >= 0
    ensures
        hexNum == n * ((2 * n) - 1)
;

proof fn lemma_NthHexagonalNumber(n: int) -> (hexNum: int)
    requires
        n >= 0
    ensures
        hexNum == n * ((2 * n) - 1)
{
    0
}

}