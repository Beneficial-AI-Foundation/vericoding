// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    48 <= c as int <= 57
}

spec fn spec_CountSubstringsWithSumOfDigitsEqualToLength(s: String) -> count: int
    ensures
        count >= 0
;

proof fn lemma_CountSubstringsWithSumOfDigitsEqualToLength(s: String) -> (count: int)
    ensures
        count >= 0
{
    0
}

}