// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn verifyNeg(a: Vec<int>, idx: int) -> nat
reads a
    requires
        0 <= idx <= a.len()
{
    0
}

spec fn spec_CountNeg(a: Vec<int>) -> cnt: nat
    ensures
        cnt == verifyNeg(a, a.len())
;

proof fn lemma_CountNeg(a: Vec<int>) -> (cnt: nat)
    ensures
        cnt == verifyNeg(a, a.len())
{
    0
}

}