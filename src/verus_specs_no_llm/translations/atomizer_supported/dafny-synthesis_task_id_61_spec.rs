// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn IsDigit(c: char) -> bool {
    48 <= c as int <= 57
}

fn CountSubstringsWithSumOfDigitsEqualToLength(s: String) -> (count: int)
    ensures count >= 0
{
}

}