// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn R(n: nat) -> nat
{
    0
}

spec fn spec_calcR(n: nat) -> r: nat
    ensures
        r == R(n)
;

proof fn lemma_calcR(n: nat) -> (r: nat)
    ensures
        r == R(n)
{
    0
}

}