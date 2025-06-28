// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SumOfDigits(number: nat) -> (sum: nat)
    requires
        number >= 0
    ensures
        sum >= 0,
        sum == SumDigits(number)
{
    return 0;
}

}