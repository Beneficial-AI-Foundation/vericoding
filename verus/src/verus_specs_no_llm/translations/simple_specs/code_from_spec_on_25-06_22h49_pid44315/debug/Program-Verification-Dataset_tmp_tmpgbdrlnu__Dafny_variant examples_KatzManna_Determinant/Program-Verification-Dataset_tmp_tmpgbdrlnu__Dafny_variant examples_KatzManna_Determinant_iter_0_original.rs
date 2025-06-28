// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Determinant(X: array2<int>, M: int) -> (z: int)
    requires
        1 <= M,
        X != null && M == X.Length0 && M == X.Length1
 modifies X
{
    return 0;
}

}