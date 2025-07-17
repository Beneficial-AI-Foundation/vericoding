// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_NthDecagonalNumber(n: int) -> decagonal: int
    requires
        n >= 0
    ensures
        decagonal == 4 * n * n - 3 * n
;

proof fn lemma_NthDecagonalNumber(n: int) -> (decagonal: int)
    requires
        n >= 0
    ensures
        decagonal == 4 * n * n - 3 * n
{
    0
}

}