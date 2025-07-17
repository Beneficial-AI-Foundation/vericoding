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

spec fn spec_ComputePower(N: int) -> y: nat
    requires
        N >= 0
    ensures
        y == Power(N)
;

proof fn lemma_ComputePower(N: int) -> (y: nat)
    requires
        N >= 0
    ensures
        y == Power(N)
{
    0
}

}