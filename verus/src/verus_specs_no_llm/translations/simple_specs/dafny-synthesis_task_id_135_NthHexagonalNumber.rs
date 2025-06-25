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

fn NthHexagonalNumber(n: int) -> (hexNum: int)
    requires
        n >= 0
    ensures
        hexNum == n * ((2 * n) - 1)
{
    return 0;
}

}