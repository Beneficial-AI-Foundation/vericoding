// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sum(n: nat) -> nat
{
    0
}

spec fn spec_sumBackwards(n: nat) -> r: nat
    ensures
        r == sum(n)
;

proof fn lemma_sumBackwards(n: nat) -> (r: nat)
    ensures
        r == sum(n)
{
    0
}

}