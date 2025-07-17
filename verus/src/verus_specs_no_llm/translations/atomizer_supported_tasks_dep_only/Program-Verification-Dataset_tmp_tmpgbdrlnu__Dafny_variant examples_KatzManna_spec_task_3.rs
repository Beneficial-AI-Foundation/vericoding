// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Determinant(X: array2<int>, M: int) -> z: int
    requires
        1 <= M,
        X != null && M == X.Length0 && M == X.Length1
;

proof fn lemma_Determinant(X: array2<int>, M: int) -> (z: int)
    requires
        1 <= M,
        X != null && M == X.Length0 && M == X.Length1
{
    0
}

}