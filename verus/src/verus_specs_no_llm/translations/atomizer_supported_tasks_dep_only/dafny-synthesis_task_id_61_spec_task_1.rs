// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    48 <= c as int <= 57
}

fn CountSubstringsWithSumOfDigitsEqualToLength(s: String) -> (count: int)
    ensures
        count >= 0
{
    return 0;
}

}