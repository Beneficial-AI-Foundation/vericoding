// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn C(n: nat) -> nat
{
    0
}

spec fn spec_calcC(n: nat) -> res: nat
    ensures
        res == C(n)
;

proof fn lemma_calcC(n: nat) -> (res: nat)
    ensures
        res == C(n)
{
    0
}

}