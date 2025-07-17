// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_SquareRoot(N: nat) -> r:nat
    ensures
        r*r <= N < (r+1)*(r+1)
;

proof fn lemma_SquareRoot(N: nat) -> (r: nat)
    ensures
        r*r <= N < (r+1)*(r+1)
{
    0
}

}