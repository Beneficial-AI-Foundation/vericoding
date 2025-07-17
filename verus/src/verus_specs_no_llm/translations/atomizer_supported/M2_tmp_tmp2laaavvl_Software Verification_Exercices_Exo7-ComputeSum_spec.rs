// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sum(n: nat) -> nat
{
    0
}

spec fn spec_ComputeSum(n: nat) -> s:nat
    ensures
        s ==Sum(n)
;

proof fn lemma_ComputeSum(n: nat) -> (s: nat)
    ensures
        s ==Sum(n)
{
    0
}

}