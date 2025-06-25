// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Determinant(X: array2<int>, M: int) -> (z: int)
    requires 1 <= M;,
             X != null and M == X.Length0 and M == X.Length1;
  modifies X;
{
}

}