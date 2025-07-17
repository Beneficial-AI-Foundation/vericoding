// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CenteredHexagonalNumber(n: nat) -> result: nat
    requires
        n >= 0
    ensures
        result == 3 * n * (n - 1) + 1
;

proof fn lemma_CenteredHexagonalNumber(n: nat) -> (result: nat)
    requires
        n >= 0
    ensures
        result == 3 * n * (n - 1) + 1
{
    0
}

}