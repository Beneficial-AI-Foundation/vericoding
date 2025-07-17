// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn fact(n: nat) -> nat
{
    0
}

spec fn spec_factIter(n: nat) -> a:nat
    requires
        n >= 0
    ensures
        a == fact(n)
;

proof fn lemma_factIter(n: nat) -> (a: nat)
    requires
        n >= 0
    ensures
        a == fact(n)
{
    0
}

}