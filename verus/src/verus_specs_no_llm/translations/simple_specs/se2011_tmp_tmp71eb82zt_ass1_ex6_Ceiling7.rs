// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Ceiling7(n: nat) -> k:nat
    requires
        n >= 0
    ensures
        k == n-(n%7)
;

proof fn lemma_Ceiling7(n: nat) -> (k: nat)
    requires
        n >= 0
    ensures
        k == n-(n%7)
{
    0
}

}