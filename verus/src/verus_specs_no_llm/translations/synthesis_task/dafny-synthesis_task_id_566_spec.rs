// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

proof fn ValuesOfn(number: nat, ndigits: nat) -> ((r: Seq<nat>)
{
    Seq::empty()
}

spec fn spec_SumOfDigits(number: nat) -> sum: nat
    requires
        number >= 0
    ensures
        sum >= 0,
        sum == SumDigits(number)
;

proof fn lemma_SumOfDigits(number: nat) -> (sum: nat)
    requires
        number >= 0
    ensures
        sum >= 0,
        sum == SumDigits(number)
{
    0
}

}