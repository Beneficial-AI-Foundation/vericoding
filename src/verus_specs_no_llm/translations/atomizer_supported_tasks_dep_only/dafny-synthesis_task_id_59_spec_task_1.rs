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

fn NthOctagonalNumber(n: int) -> (octagonalNumber: int)
    requires
        n >= 0
    ensures
        octagonalNumber == n * (3 * n - 2)
{
    return 0;
}

}