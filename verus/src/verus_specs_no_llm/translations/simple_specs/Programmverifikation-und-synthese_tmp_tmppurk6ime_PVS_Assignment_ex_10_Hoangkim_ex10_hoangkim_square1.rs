// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_square1(n: nat) -> sqn : nat
    ensures
        sqn == n*n
;

proof fn lemma_square1(n: nat) -> (sqn: nat)
    ensures
        sqn == n*n
{
    0
}

}