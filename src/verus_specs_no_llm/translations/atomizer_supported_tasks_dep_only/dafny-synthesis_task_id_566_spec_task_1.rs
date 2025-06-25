// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SumOfDigits(number: nat) -> (sum: nat)
    requires number >= 0
    ensures sum >= 0,
            sum == SumDigits(number)
{
}

}