// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Power(n: nat) -> nat
{
    0
}

spec fn spec_ComputePower(n: nat) -> p: nat
    ensures
        p == Power(n)
;

proof fn lemma_ComputePower(n: nat) -> (p: nat)
    ensures
        p == Power(n)
{
    0
}

}