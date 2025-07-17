// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_sumOdds(n: nat) -> sum:nat
    ensures
        sum == n*n
;

proof fn lemma_sumOdds(n: nat) -> (sum: nat)
    ensures
        sum == n*n
{
    0
}

}