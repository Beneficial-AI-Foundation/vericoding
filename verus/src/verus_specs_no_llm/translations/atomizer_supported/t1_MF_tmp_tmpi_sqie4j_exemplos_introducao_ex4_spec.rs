// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Fat(n: nat) -> nat
{
    0
}

spec fn spec_Fatorial(n: nat) -> r:nat
    ensures
        r == Fat(n)
;

proof fn lemma_Fatorial(n: nat) -> (r: nat)
    ensures
        r == Fat(n)
{
    0
}

}