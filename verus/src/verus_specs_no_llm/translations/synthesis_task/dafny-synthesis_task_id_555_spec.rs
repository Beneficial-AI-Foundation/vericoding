// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_DifferenceSumCubesAndSumNumbers(n: int) -> diff: int
    requires
        n >= 0
    ensures
        diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
;

proof fn lemma_DifferenceSumCubesAndSumNumbers(n: int) -> (diff: int)
    requires
        n >= 0
    ensures
        diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
    0
}

}