// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn DoubleQuadruple(x: int) -> (a: int, b: int)
    ensures
        a == 2 * x && b == 4 * x
{
    return (0, 0);
}

}