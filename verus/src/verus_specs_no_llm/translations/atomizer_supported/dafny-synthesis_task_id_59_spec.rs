// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_NthOctagonalNumber(n: int) -> octagonalNumber: int
    requires
        n >= 0
    ensures
        octagonalNumber == n * (3 * n - 2)
;

proof fn lemma_NthOctagonalNumber(n: int) -> (octagonalNumber: int)
    requires
        n >= 0
    ensures
        octagonalNumber == n * (3 * n - 2)
{
    0
}

}