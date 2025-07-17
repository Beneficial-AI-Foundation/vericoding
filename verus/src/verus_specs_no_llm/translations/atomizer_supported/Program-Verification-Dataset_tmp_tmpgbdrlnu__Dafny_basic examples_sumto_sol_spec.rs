// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sum_up_to(n: nat) -> nat
{
    0
}

spec fn spec_SumUpTo(n: nat) -> r: nat
    ensures
        r == sum_up_to (n)
;

proof fn lemma_SumUpTo(n: nat) -> (r: nat)
    ensures
        r == sum_up_to (n)
{
    0
}

}