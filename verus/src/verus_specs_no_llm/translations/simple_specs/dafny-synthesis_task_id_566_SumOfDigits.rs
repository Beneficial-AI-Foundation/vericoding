// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn SumDigitsRecursive(n: nat, p: nat) -> (r: nat)
{
    0
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