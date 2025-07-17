// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn calcSum(n: nat) -> nat
{
    0
}

spec fn spec_sum(n: nat) -> s: nat
    ensures
        s == calcSum(n + 1)
;

proof fn lemma_sum(n: nat) -> (s: nat)
    ensures
        s == calcSum(n + 1)
{
    0
}

}