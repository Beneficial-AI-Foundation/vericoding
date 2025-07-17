// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn F(n: nat) -> nat
{
    0
}

spec fn spec_calcF(n: nat) -> res: nat
    ensures
        res == F(n)
;

proof fn lemma_calcF(n: nat) -> (res: nat)
    ensures
        res == F(n)
{
    0
}

}