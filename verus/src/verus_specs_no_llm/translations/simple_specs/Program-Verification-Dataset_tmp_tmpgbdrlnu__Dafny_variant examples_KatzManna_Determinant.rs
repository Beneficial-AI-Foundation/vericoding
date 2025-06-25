// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
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