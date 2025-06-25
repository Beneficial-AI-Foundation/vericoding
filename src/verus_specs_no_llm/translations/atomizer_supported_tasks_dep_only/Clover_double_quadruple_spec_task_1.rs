// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn DoubleQuadruple(x: int) -> a: int, b: int
    ensures a == 2 * x and b == 4 * x
{
}

}