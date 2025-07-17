// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_NthNonagonalNumber(n: int) -> number: int
    requires
        n >= 0
    ensures
        number == n * (7 * n - 5) / 2
;

proof fn lemma_NthNonagonalNumber(n: int) -> (number: int)
    requires
        n >= 0
    ensures
        number == n * (7 * n - 5) / 2
{
    0
}

}