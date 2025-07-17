// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_SumOfFourthPowerOfOddNumbers(n: int) -> sum: int
    requires
        n > 0
    ensures
        sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n  - 14 * n + 7) / 15
;

proof fn lemma_SumOfFourthPowerOfOddNumbers(n: int) -> (sum: int)
    requires
        n > 0
    ensures
        sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n  - 14 * n + 7) / 15
{
    0
}

}