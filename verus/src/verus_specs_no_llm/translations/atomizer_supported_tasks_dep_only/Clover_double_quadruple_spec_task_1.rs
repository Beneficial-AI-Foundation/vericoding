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

fn DoubleQuadruple(x: int) -> (a: int, b: int)
    ensures
        a == 2 * x && b == 4 * x
{
    return (0, 0);
}

}